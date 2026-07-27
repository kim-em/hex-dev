# hex-interval-mathlib (real semantics, verified propagators, and the `interval` tactic)

`hex-interval-mathlib` gives mathematical meaning to
[hex-interval](hex-interval.md), proves soundness theorems for interval
propagators, and provides the `interval` tactic. It depends on Mathlib and
`hex-interval`. There is no separate proof-only companion beyond this library.

The tactic proves bounds for ordinary Lean expressions over `ℝ`. It reads
bounds from the local context, reifies shared expressions to a static
single-assignment program, runs the compiled `hex-interval` search, and turns
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

## User contract

The main tactic is best-effort:

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

def Lower.Holds : Lower → ℝ → Prop
  | .unbounded, _      => True
  | .finite a false, x => (a.toRat : ℝ) ≤ x
  | .finite a true,  x => (a.toRat : ℝ) < x

def Upper.Holds : Upper → ℝ → Prop
  | .finite b false, x => x ≤ (b.toRat : ℝ)
  | .finite b true,  x => x < (b.toRat : ℝ)
  | .unbounded, _      => True

end Interval

def Interval.Mem (I : Interval) (x : ℝ) : Prop :=
  match I.repr with
  | .empty        => False
  | .bounds lo hi => lo.Holds x ∧ hi.Holds x

end Hex
```

The notation `x ∈ᵢ I` is local to this library. The public conversion lemmas
identify each normalized shape with the corresponding Mathlib set interval.
Infinities are endpoint markers, not real values.

The foundational theorems are:

```lean
theorem mem_intersect : x ∈ᵢ I → x ∈ᵢ J → x ∈ᵢ intersect I J
theorem mem_hull_left  : x ∈ᵢ I → x ∈ᵢ hull I J
theorem mem_hull_right : x ∈ᵢ J → x ∈ᵢ hull I J
theorem split_cover : x ∈ᵢ I → x ∈ᵢ (split I m).1 ∨ x ∈ᵢ (split I m).2
theorem not_mem_empty : ¬x ∈ᵢ .empty
```

Each arithmetic operation has an image theorem. Representative shapes are:

```lean
theorem mem_add : x ∈ᵢ I → y ∈ᵢ J → x + y ∈ᵢ add I J
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

Every kernel-facing checker uses structural recursion or an explicit natural
fuel whose decrease is visible after reduction. A checker must not hide a
well-founded recursion whose proof terms block ordinary kernel evaluation.
This applies in particular to logarithm and bit-precision helpers. Compiled
and kernel evaluation are benchmarked separately before a checker is admitted
to generated proofs.

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

## Program semantics and the golden theorem

The reified program is an array of typed instructions whose arguments refer to
earlier entries. A valuation assigns real values to free-variable nodes. The
program's `OpKey` table gives each instruction its real meaning; a chosen
`RuleKey` is only a method for enclosing that meaning.

The natural checker does not interpret arbitrary operation keys from the
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
- a stable rule name and natural certificate-schema version, together forming
  the `RuleKey` used in diagnostics and replay traces.

For a simple rule, the soundness theorem has this form:

```lean
theorem add_check_sound
    (hcheck : addCheck I J out payload = true) :
    x ∈ᵢ I → y ∈ᵢ J → x + y ∈ᵢ out
```

For a theorem whose output is already a transparent function of its inputs,
the registration may apply `mem_add` directly and omit `payload`. A Taylor
rule instead stores its polynomial degree, reduced argument, endpoint values,
and remainder witness, then uses a checker theorem for those fields.

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
- `abs`, `min`, `max`, and `Real.sqrt`;
- named real constants with registered nullary rules;
- registered unary and binary functions.

The first elementary-function milestone adds `Real.exp`, `Real.log`,
`Real.sin`, `Real.cos`, `Real.atan`, and `Real.rpow` on proved positive bases.
The LeanCert compatibility milestone then audits the rest of the expression
heads its downstream users need, including hyperbolic functions, `arsinh`,
`atanh`, `sinc`, and `erf`. A name in the reified language is not considered
supported until at least one sound propagator covers its stated domain.

### Context facts

The frontend recognizes:

- strict and non-strict comparisons with rational expressions;
- equality as two closed bounds;
- all finite and one-sided `Set.Ixx` membership forms;
- conjunctions of recognized facts;
- local definitions that are definitionally equal after elaboration.

Facts about arbitrary derived terms are retained. They are not restricted to
free variables. Unknown hypotheses remain in the context but do not enter the
interval program.

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
tactics. It returns the dyadic search interval, any stronger exact rational
source cuts, proof expressions for the selected global bounds, and search
diagnostics.
This is the future integration seam. This SPEC does not register it with
`grind`.

### Configuration

The stable configuration fields are:

```lean
structure Interval.Config where
  policy         : Name := `balancedV1
  maxProgramNodes : Nat
  maxFormsPerNode : Nat
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

The implementation also has an emergency timeout, but test expectations and
successful replay do not depend on a particular machine reaching it.

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
rules and a sound coarse fallback. Square root uses monotonicity on nonnegative
inputs and accounts for Mathlib's value on negative inputs when the interval
is not known nonnegative.

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
5. round the final cut outward to the requested dyadic precision.

The certificate contains the reduction parameters, approximation order,
endpoint values, and remainder witness. The planner selects them. The checker
verifies them.

### Sine and cosine

The initial sine rule follows the existing experiment on `[-1,1]`: evaluate a
rational Taylor polynomial and bound the Lagrange remainder. The implementation
uses dyadic endpoints in its hot arithmetic and retains the experiment's
Mathlib proof of the analytic remainder.

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
tree. The initial chunk ceiling is selected by batch-replay measurements. It is not
hard-coded by this SPEC. This avoids both a linear-depth proof term and one
enormous Boolean reduction. Kernel-facing recursive checkers use exposed
definitions and reduction-stable payload types. They do not rely on opaque
array equality reduction across module boundaries.

The BKLNW sums with upper limits 29, 37, 63, 145, 289, and 433 are the scaling
ladder. Their index set is `Icc 3 N`, so they contain `N - 2` summands. The
13,590-cell FKS2 corpus is the large-batch acceptance test.

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
  implementation replaced it. This is the reason for the checker recursion
  rule above.
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

The working endpoint choice remains empirical. This SPEC selects arbitrary
dyadics for propagated facts and preserves exact rational source facts. The
backend-comparison milestone compares that hybrid against a separate exact
rational search prototype with deliberate regularization on tactic-scale
examples. The public search protocol and certificate concepts should not
prevent a later representation revision if measured proof cost favors the
rational variant.

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

The inspected LeanCert snapshot is
[`31579b5`](https://github.com/alerad/leancert/tree/31579b55618d11e4fbe622a6b5e30b0359b2ee6d).
The inspected PNT+ snapshot is
[`be5e07e`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/be5e07e04cde20c5ceabf63759bd097a9c88173f).
Its
[lakefile](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/be5e07e04cde20c5ceabf63759bd097a9c88173f/lakefile.toml)
pins LeanCert `v4.32.1` at commit `87a21d7`. The differences from the inspected
LeanCert main snapshot do not change the interval representation or trust
findings below.

The useful LeanCert ideas are a small semantic expression language, a golden
soundness theorem, exact rational and dyadic evaluators, affine arithmetic,
derivative-sign pruning, and untrusted discovery followed by checked
evaluation. The replacement keeps those ideas.

The following limitations become explicit requirements here.

- Practical LeanCert tactics usually close checks with `native_decide`. The
  pinned audit shows `Lean.ofReduceBool` plus a fresh generated declaration
  matching `<decl>._native.native_decide.ax_*`; reliance on compiled
  evaluation is the trust issue, while `Lean.trustCompiler` is not listed as a
  direct dependency of those audited theorems. This library excludes all of
  these paths.
- `IntervalRat` represents only nonempty finite closed intervals. This library
  represents empty, open, half-open, and unbounded intervals.
- Backend choice is mostly static. This library measures rule outcomes and can
  escalate precision, form, rewriting, propagation, or subdivision.
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

At the pinned snapshot it contains about 280 actual `interval_decide`
invocations across 15 files. Compatibility must therefore be tested by
maintaining source-pinned copies of representative statements and expression
definitions with their LeanCert calls replaced. Merely importing an upstream
declaration whose existing proof already used compiler trust does not test the
replacement. A few translated README examples are also insufficient.

- [LogTables.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/be5e07e04cde20c5ceabf63759bd097a9c88173f/PrimeNumberTheoremAnd/IEANTN/LogTables.lean)
  contains hundreds of `exp` and `log` point bounds, nested logs, large
  arguments, and errors down to about `10^-100`.
- [BKLNW_a2_bounds.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/be5e07e04cde20c5ceabf63759bd097a9c88173f/PrimeNumberTheoremAnd/IEANTN/BKLNW/BKLNW_a2_bounds.lean)
  contains finite sums whose certified upper limits reach 433.
- BKLNW Table 10 contains sums of exponentials with small margins. PNT+ PR
  [#1510](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/pull/1510)
  records a false target exposed numerically. Failure diagnostics must report
  the incompatible enclosure rather than only request more precision.
- PNT+ PR [#1405](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/pull/1405)
  records manual treatment of `exp (-log N / k)` and a theorem containing
  roughly 135 interval checks. It also records four false original boundary
  rows, at `b = log(5e10)`, `25`, `log(3.2e13)`, and `32`; at least one
  original row remains an expected-failure regression. These cases motivate
  certified normalization, batch replay, and useful failure bounds.
- [Table4ExtCore.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/be5e07e04cde20c5ceabf63759bd097a9c88173f/PrimeNumberTheoremAnd/IEANTN/FKS2Tables/Table4ExtCore.lean)
  defines the generic cell checker and its transport theorem. The 13,590 cells
  live in
  [fourteen `Table4ExtData_*` shards](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/be5e07e04cde20c5ceabf63759bd097a9c88173f/PrimeNumberTheoremAnd/IEANTN/FKS2Tables),
  thirteen of size 1,000 and one of size 590, and
  [Table4Ext.lean](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/be5e07e04cde20c5ceabf63759bd097a9c88173f/PrimeNumberTheoremAnd/IEANTN/FKS2Tables/Table4Ext.lean)
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

### Lessons from other systems

| System or method | Adopted lesson | Deliberate limit |
| --- | --- | --- |
| IEEE 1788 | Separate mathematical sets, finite endpoint data, and encoding. Include empty and unbounded cases. | Its set flavor does not represent open endpoints, so it does not determine the Lean type. |
| CoqInterval | Shared straight-line programs, reflection, automatic differentiation, Taylor bounds, and subdivision are all practical in a proof assistant. | The initial implementation uses a hybrid replay rather than copying one monolithic evaluator. |
| Gappa and Sollya | Untrusted search can propose rewrites, polynomial bounds, and subdivisions for a small proof checker. Best-bound diagnostics are valuable. | They are optional proposal sources only. Lean replay remains independent. |
| MPFR and MPFI | Arbitrary precision, directed rounding, and argument reduction guide endpoint algorithms. | Hardware rounding state and foreign results are not trusted. |
| Arb | Midpoint-radius balls and cached high-precision point evaluation are efficient for narrow inputs. | Balls are an internal candidate representation. Public semantics remain endpoint intervals because balls do not express open or half-infinite sets. |
| IBEX HC4 | Dependency worklists, forward-backward contractors, contraction thresholds, smear scores, and split policies transfer directly. | Constraint solving heuristics never justify a Lean fact by themselves. |
| HOL Light nonlinear verification | Monotonicity, convexity, boundary reuse, and certificate DAGs can scale to hard inequalities. | Full Flyspeck-style second-order verification is a later milestone. |
| Affine arithmetic | Noise symbols retain first-order correlations and are formally verifiable. | Open and unbounded sets stay in the endpoint layer. Affine forms are a later method. |
| Taylor models | Polynomial plus rigorous remainder is the strongest planned dependency-control method. | Full multivariate Taylor models do not block the first release. |
| dReal-style interval constraint propagation | Counterexample boxes, contractor scheduling, and influence-based branching are useful search ideas. | The tactic proves exact Lean propositions. It does not use delta weakening. |

## Regression and challenge corpus

Each case records the required feature, expected success or safe failure,
selected policy, search statistics, replay time, certificate size, and axiom
set. Exact imported statements are pinned to upstream commits when licensing
permits copying them into test modules.

### Endpoint semantics

- all four closure combinations at finite ends;
- both one-sided unbounded shapes and the whole interval;
- singleton normalization and the three empty equal-endpoint shapes;
- strict conclusion from one open summand, such as
  `x ∈ (0,1), y ∈ [0,1] ⟹ x + y < 2`;
- reciprocal on positive open and half-open intervals, including the outward
  dyadic enclosure of `{3}⁻¹ = {1/3}` at two precisions;
- inverse and division across zero, including Lean's value at zero;
- logarithm at, below, and just above zero;
- a split whose cut equals a parent endpoint.

### Arithmetic and dependency

```lean
x - x = 0
x ∈ [0,1]             ⟹ x * (1 - x) ≤ 1/4
x ∈ [-1,1]            ⟹ x^2 ≤ 1
x ∈ (0,+∞)            ⟹ 0 < x / (x + 1)
x ∈ [0,1], y ∈ [0,1]  ⟹ (x+y)*x + (x+y) ≥ 0
```

These cases distinguish proved same-node cancellation, centered forms,
contractors, and subdivision from naive repeated interval evaluation. Sharing
alone does not prove `x - x = 0`; the exact cancellation alternate does.

Additional coordination and handoff cases are:

- `x^2 + y^2 = 1 ⟹ x^4 + y^4 ≤ 1`, which needs information to move from a
  nonlinear equality into the forward bounds;
- `y * 2 - y * Real.sqrt 2 ^ 2 ≤ 0`, using
  `Real.sq_sqrt zero_le_two` before the linear arithmetic handoff;
- the four-corner multiplication theorem: from `a ≤ u ≤ b`, `c ≤ v ≤ d`,
  and a lower bound below all four products `a*c`, `a*d`, `b*c`, `b*d`, prove
  that it is below `u*v`;
- `0 ≤ 1 - 3*x^2*y^2 + x^2*y^4 + x^4*y^2` as a handoff case. A polynomial
  certificate tactic can solve the residual, while plain intervals over
  unbounded variables should decline it;
- a deterministic synthetic generator parameterized by variable count,
  irrelevant linear constraints, and constraints of the form `ν ≤ max a b`.
  Its known solution uses a small active subset while the number of apparent
  max branches grows rapidly. It tests split planning without reproducing an
  unpublished application statement or its identifying dimensions.

### Elementary functions

- the sine experiment's point bounds
  `-25/48 ≤ sin (-1/2)` and `sin (1/3) ≤ 637/1944`;
- `|sin x| ≤ 1` on an unbounded input;
- a narrow sine interval crossing a critical point;
- a large-argument sine that uses periodic reduction;
- exact `sin π = 0` through a symbolic rewrite;
- `exp x ≥ 1 + x` on `[0,+∞)` through derivative monotonicity;
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

### PNT+ compatibility

The committed compatibility subset includes:

- two-sided `log 2` and `log 3` bounds;
- the one-sided nested bound `0.633415 < log (log 6.58)` and the two-sided
  bound `-0.366513 ≤ log (log 2) ≤ -0.366512`;
- `exp (-1)`, `exp (-1/2)`, and `exp (-2/3)`;
- `log 11723 ≤ 9.37`, `exp 20 ≤ 485165196`, and
  `10^9 ≤ exp 22`;
- representative `10^-20` and `10^-100` tail bounds;
- BKLNW sums with upper limits 29, 37, 63, 145, 289, and 433;
- one Table 10 shard and the recorded false target as an expected failure;
- the approximately 135-case Table 12 batch, plus one of its four false
  original boundary rows as an expected failure;
- a small, medium, and complete 13,590-cell FKS2 batch;
- mutated Taylor, range-reduction, fold, and split certificates, all rejected.

The [PNT+ log-table generator](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/be5e07e04cde20c5ceabf63759bd097a9c88173f/scripts/gen_log_tables.py)
is a model for optional untrusted candidate generation. The committed tests
still exercise the native Lean planner and replay path.

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

## Conformance

The required Lean-only checks include:

- semantic theorems for every interval operation and endpoint shape;
- one direct and one certificate-backed propagator registration;
- failure of a deliberately corrupted registration payload;
- rejection of out-of-range operation, node, fact, and payload identifiers;
- rejection of a wrong input side or fact version, sibling or non-ancestor
  dependencies, cyclic or multiply-parented scopes, a mismatched split
  assumption, and a `Close.goal` whose facts do not imply the target;
- raw-expression reification for casts, decimals, powers, `abs`, shared terms,
  and finite folds;
- goal closure for strict, non-strict, equality, disequality, membership,
  contradiction, and conjunction targets;
- safe refusal for an unsupported function and an exhausted budget;
- a proof axiom audit excluding compiler trust and `sorryAx`;
- proof sharing across repeated subexpressions and split branches;
- chunked fold replay at every chunk boundary.

Every malformed-trace case must fail before the tactic assigns the user's
goal metavariable.

The external oracle profile uses `python-flint` Arb for independently computed
point and elementary-function enclosures. A fixture fixes an input box and a
coarse rational target. Lean proves that the function image lies in the target.
Arb independently encloses the complete closed input ball at higher precision
and checks that its enclosure also lies in the same target. Separate fixtures
sample deterministic rational points and exercise known extrema and domain
boundaries. This is bug-finding evidence, not a proof and not a runtime
dependency. CoqInterval or MPFI comparison runs may be local informational
tests.

## Performance acceptance

The test harness records four times separately:

1. compiled planning and propagator execution;
2. proof expression construction;
3. elaboration and kernel replay;
4. incremental rebuild of a file importing the finished theorem.

It also records allocations, program nodes, accepted actions, rule calls,
splits, leaves, maximum endpoint heights, certificate bytes, proof nodes, and
object-file size.

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
- the complete FKS2 corpus: bounded per-cell certificate size, shared static
  data, and no theorem or object-file blowup proportional to duplicated
  transcendental tables.

The LeanCert version pinned by PNT+ is a migration baseline. The new tactic is
not declared a replacement until it proves the selected downstream corpus,
passes the stricter axiom audit, and improves either total time or artifact
size on every large tier without a serious regression on the other measure.

## Development order

1. Prove interval semantics, normalization, arithmetic enclosure, rational
   projection, regularization, and split coverage.
2. Before freezing checker or trace formats, build a narrow vertical
   feasibility prototype for one small arithmetic DAG, the BKLNW fold with
   upper limit 433, and one high-precision `exp` or `log` certificate. For each,
   record compiled checking, proof construction, kernel replay, transitive
   axioms, proof and object bytes, and incremental import time. Failure to make
   ordinary kernel replay practical changes the architecture before wider
   implementation.
3. Implement the production shared program, natural evaluator, generic
   soundness theorem, reifier, and scoped proof slicer for arithmetic over
   `ℝ`.
4. Add the explicit rule registry, multiple methods per head, diagnostics, and
   the `interval` and `interval_bound` frontends.
5. Port the sine experiment to dyadic endpoints. Add stateful Taylor
   certificates and the triple-angle rewrite.
6. Add centered automatic differentiation, derivative-sign monotonicity, and
   dependency-aware backward propagation.
7. Add `π`, `exp`, `log`, square root, `atan`, positive-base real powers,
   certified range reduction, and symbolic special values.
8. Add production chunked folds and the PNT+ point and sum corpus. Remove every
   need for a `native_decide` proof path in the selected compatibility files.
9. Add arbitrary and function-suggested subdivision, then the Table 10, Table
   12, FKS2, and complete IMO partition tiers.
10. Compare Bernstein, second-order, affine, and Taylor-model methods on the
    challenge corpus before selecting further defaults.

Every stage has real executable definitions and tests for its advertised
surface. Unimplemented methods remain absent rather than returning ceremonial
wide answers that masquerade as the intended algorithm.

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
    suggestions produce better gain per proof node than backward contractors?

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
  migrated downstream regressions.
- `conformance/HexIntervalMathlib/EmitFixtures.lean`: elementary-function
  fixtures for the external oracle.

Unlike a correspondence-only companion, `hex-interval-mathlib` contains an
executable reifier, rule registry, and tactic. Its own conformance target tests
that runtime-facing API while keeping the released Mathlib-free conformance
target free of Mathlib imports. Small explanatory examples remain in
`Examples.lean`; the bulk PNT+, nonlinear, and challenge corpus belongs in the
companion conformance project and is built in CI.

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
- [Isabelle verified affine arithmetic](https://isa-afp.org/entries/Affine_Arithmetic.html)
  and [verified Taylor models](https://isa-afp.org/entries/Taylor_Models.html).
- Lawrence Paulson,
  [MetiTarski: past and future](https://www.cl.cam.ac.uk/~lp15/papers/Arith/calculemus2008.pdf).
- Sicun Gao, Jeremy Avigad, and Edmund Clarke,
  [Delta-complete decision procedures for satisfiability over the reals](https://arxiv.org/abs/1204.3513).
- [IntervalArithmetic.jl documentation](https://juliaintervals.github.io/IntervalArithmetic.jl/stable/).
- LeanCert at
  [`31579b5`](https://github.com/alerad/leancert/tree/31579b55618d11e4fbe622a6b5e30b0359b2ee6d)
  and PNT+ at
  [`be5e07e`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/be5e07e04cde20c5ceabf63759bd097a9c88173f).
