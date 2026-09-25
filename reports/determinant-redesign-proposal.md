# Determinant architecture and replacement proposal

This is a proposal for implementation, not an amendment already in force.
[Measurements and counterexamples](determinant-redesign-results.md) and
[reproducible prototypes](../experiments/Determinant/README.md) support the
choices below. The experiments do not establish universal superiority or
production selection thresholds.

## Recommendation

Separate three operations: computing an exact value, constructing a symbolic
result in an explicitly requested representation, and proving equality to a
supplied expression. Do not require them to construct the same witness or use
the same determinant algorithm. Share algebraic theorems and coefficient
operations where useful; do not mandate a universal intermediate interpreter.
The symbolic-result contract is a design hypothesis: the proof experiments
all receive a supplied target and do not measure constructing an expanded
result. Result-producing consumers require their own evidence before migration.

For symbolic proofs, investigate a general division-free backend with cached
proof-producing arithmetic. The
[adversarial search](determinant-adversarial-search.md) finds substantial losses
for unconditional deferral, including inputs Mathlib proves in under a minute
while the shared-expression prototype times out. The
[normalized comparison](determinant-normalized-comparison.md) supports reusing
Mathlib's normalized Bird evaluator, retaining its atom context for the target,
and returning its certificate directly when the target is already definitionally
equal to the normal form. Extend the final variant's adversarial coverage before
choosing the production backend; its 10×10 rank-one case still loses to Mathlib.
This borrows
the mathematics and scalar proof machinery of Mathlib directly. It does not call `norm_det`,
`eval_det`, or any hidden determinant fallback. Importing Mathlib arithmetic
lemmas in the companion is compatible with Mathlib-free computational libraries.

For exact values, retain fraction-free elimination while improving coefficient
representation and native modular kernels. Integer Bareiss remains the control;
exact rational/dyadic scaling is the first coefficient adapter to implement.
Dense univariate polynomial arithmetic deserves a distinct representation from
sparse multivariate arithmetic. Modular value performance needs a fast inner
loop before another dispatcher can usefully select it.

These are two implementation efforts, not an argument for deleting the current
stack in one change. The numeric certificate path, determinant theory and
shared algebraic interfaces have demonstrated uses and should survive.

| Component | Decision | Evidence or condition |
|---|---|---|
| Leibniz reference determinant and matrix identities | Retain | Independent specification and downstream theorem base |
| Integer Bareiss value routine | Retain as baseline and available method | Beats the tested Lean Bird/Berkowitz and modular methods on dense integers |
| Numeric determinant certificates | Retain | Symbolic experiments do not invalidate their measured numeric advantages |
| Polynomial triangular witness as the mandatory symbolic backend | Replace as a requirement | Fixed-witness proof construction loses after arithmetic and transport improvements |
| Shared Bird expressions with cached normalization | Retain as an experimental comparator; resolve normalization before migration | Wins on many dense inputs, but loses on hidden zeros and larger rank-one matrices; see the adversarial report |
| Normalized Bird certificates with direct target conversion | Extend adversarial coverage before migration | General normalization removes large cancellation losses; direct conversion wins at 16×16 rank one but still loses at 10×10 |
| Blanket opacity for reused arithmetic proofs | Reject | Additional auxiliary checking outweighs the saved outer check |
| Deferred expression followed by independent `ring` traversal | Reject as default | Loses to cached traversal on the same recurrence and target |
| Eager Bird value prototype | Do not pursue this implementation | Loses on integer/rational values; list allocation and bounds checks confound any schedule-wide conclusion |
| Existing recursive/flat modular elimination | Retain as correctness controls; replace hot execution when proved | Both remain far slower than the same-prime external comparison |
| Owned Lean array loop or raw words alone | Reject these prototypes | Neither removes the large modular gap |
| C modular word loop | Develop an `@[extern]` value implementation with a proved Lean logical model | C diagnostic closes most of the execution gap; the tested Lean buffer loops do not |
| Row scaling for rational/dyadic values | Confirm with in-process repetitions, then implement and prove | Promising cold single-call measurements include scaling and normalization |
| Direct small-degree dense polynomial arithmetic | Retain and expose to selection | Representation comparison favors it over sparse arithmetic and interpolation |
| General evaluation/interpolation framework | Defer | The small cold interpolation experiment loses; no crossover is established |

## Proposed SPEC amendments

These paragraphs are intended as concrete replacement/additional text in a
SPEC-only PR before production implementation. Existing soundness statements
remain obligations until their consumers are migrated.

### `SPEC/matrix-tactics.md`: placement and kernel discipline

Replace the rule that a tactic is a frontend to exactly one certificate with:

> A tactic owns one operation and its classification/diagnostic contract. It
> may use different proved constructions for different coefficient capabilities.
> This does not create a second public tactic or a hidden external fallback.
> A determinant algorithm used by a tactic is explicit in its route diagnostics.

Replace the universal list-only restriction with:

> Reflective arithmetic checkers use representations and structural recursion
> suited to kernel reduction. Direct algebraic proof construction is also
> permitted. A backend must justify its proof-sharing boundaries by complete
> declaration measurements, including every auxiliary check. No backend may
> obtain performance credit by moving unchecked or prechecked work outside the
> measurement. Accepted theorems use only `propext`, `Classical.choice`, and
> `Quot.sound`; `sorry`, added axioms and `native_decide` are forbidden.

Keep the existing outcome protocol, no-Mathlib-fallback rule, fresh-module
proof protocol and bar against Mathlib. Add separate value/expanded-result/
supplied-equality contracts. For result construction, name the returned
representation and include its normalization cost. Computing a small circuit
does not count as producing an expanded polynomial.

### `SPEC/Libraries/hex-poly-det.md`: instantiation and packed certificate

> `polyDet` is a value operation and does not require producing or checking a
> triangular witness. `polyDetWitness` and packed checks remain explicit
> certificate APIs while they have consumers. A symbolic equality backend may
> instead use a universally proved division-free recurrence and scalar equality
> proofs. The output contract determines whether polynomial expansion is
> required. Sparse, dense and shared-expression representations are implementation
> choices with separately measured conversion and normalization costs.

Keep bounded packing as a sufficient identity certificate, including all
degree/coefficient bounds and deterministic uniqueness. Do not require packing
for direct algebraic proofs. A few matching evaluations, stable CRT residues,
or a producer's degree guess are never a proof of polynomial equality.

### `SPEC/Libraries/hex-poly-det-mathlib.md`: routes, soundness and transport

> The general symbolic backend proves a determinant recurrence over the user's
> commutative ring and proves equality of its output expression with the supplied
> target. It must not assume cancellation or nonzero symbolic pivots. Scalar
> normalization may reuse common subexpressions and common atom indices. Proof
> construction and all kernel checks, including literal identification and target
> normalization, are included in the complete-call budget.

> Specialized determinant strategies are removed when the general backend
> covers their supported inputs within the shipping bar. Zero arithmetic,
> subexpression reuse and exact coefficient scaling are general mechanisms;
> recognising a special determinant shape is not a substitute for that backend.
> A retained certificate route needs either measured performance or a capability
> not covered by the replacement, with an explicit retirement condition.

Preserve reverse equalities, term forms, positive-characteristic coverage and
diagnostic semantics during migration. The prototype currently handles only
forward literal `Fin` matrix equalities: its API coverage is not yet production coverage.
Keep the residue term-list route until its distinct characteristic obligations
have a replacement. Generic matrix-constructor transport lemmas may replace
repeated tactic-driven entry case splits without changing the theorem claimed.

### `HexDet/SPEC/hex-det.md`: API, coefficient adapters and selection

Clarify the distinction between implemented lower modular/divisor operations
and enabled dispatch policies; their existence alone does not enable a policy.

> Exact coefficient adapters may transform the matrix before determinant
> computation and restore the result afterward. Their mathematical equations,
> nonzero scaling factors, output normalization and computational costs are part
> of the selected method. Rational row-LCM scaling and dyadic row-power-of-two
> scaling are fixed-ring adapters, not generic-field coercions or new field
> instances. Their selection statistics include numerator/denominator size or
> exponent spread where measurements show that these matter.

Retain explicit policy/route reporting and deterministic fuel/seed settings.
Do not install a modular crossover based solely on dimension or the old
structured-matrix crossover. All completed methods and exhaustion transitions
must be visible. No threshold is supplied by this exploratory report.

### `HexModularMatrix/SPEC/hex-modular-matrix.md`: one image and benchmarking

> A native modular image routine may use an `@[extern]` C implementation with
> contiguous word storage, backed by a Lean logical implementation proved to
> compute the row-pivoted determinant. The C implementation must match that model,
> supported by differential tests and explicit representation bounds. The model
> and execution implementation must agree on the determinant operation,
> including pivot sign and singular zero results. A nonunit pivot over a
> composite modulus may decline; it must not silently be treated as zero.
> Matrix storage in unrelated libraries need not change to support this kernel.

> Attribute prime discovery, bounds, residue conversion, modular elimination
> and CRT reconstruction separately when diagnosing a gap. Whole-call
> comparisons charge them all, including failed images. A precomputed prime
> supply is an explicit reusable input, not free work in a cold comparison.

Retain CRT congruences, pairwise coprimality and strict uniqueness bounds.
Retain the divisor certificate's mathematical obligations. A fast value producer
is not automatically a fast kernel checker. An external kernel requires a
logical implementation/refinement and differential tests; theorem checking
continues through proved algebraic or reflective evidence, never native evaluation.

## Staged implementation, migration and deletion

1. **Adopt the contracts.** Submit the SPEC-only changes above, reconcile the
   existing declaration inventory and preserve the public outcome protocol.
   Keep experiment commands outside default builds and CI timings. Establish
   the minimal production regression set: each retained counterexample,
   numeric integer/rational cases, zero divisors, positive characteristic,
   false targets, unsupported syntax and budget exhaustion. This is coverage,
   not a large timing grid.

2. **Resolve normalization, then build the general symbolic proof backend.**
   Extend the normalized evaluator with direct target conversion across every
   retained adversarial loss and the dense/factored controls. The initial
   measurements favor this general construction but cover only selected cases.
   Charge proof-term sharing and all kernel checks. Do not replace
   these obligations with triangular/rank-one recognition strategies. Only
   after selecting a supported construction, port it into the companion without
   importing the experimental namespace. Reuse the universal Bird correctness
   theorem, or supply the equivalent Mathlib-free theorem if the computational
   API needs it. Keep a single atom context and cache; do not copy Mathlib's
   entire scalar normalizer. Add explicit size/work budgets, reverse equalities,
   the shared literal recognizer and result-term handling. Prove/verify every
   generated declaration and audit axioms. Measure all work with the producer
   inside the call. Before committing to a schedule, compare Bareiss, Bird and
   Berkowitz on the same polynomial input with a common scalar representation
   and proof/checking method, charging Bareiss's nonzero/division obligations.
   The current value experiments control representation and external checking;
   they do not rank complete kernel-checked proofs of the three schedules.
   Bird is the first candidate because it already has a generic-ring theorem
   and a measured shared-proof prototype, not because the alternatives have
   been ruled out. Treat that proof-side comparison as an exit criterion.
   Separately measure constructing an expanded result without a supplied target,
   including expansion, normalization, result quotation and all proof checks.
   Preserve existing result-producing routes until that test passes. Require
   the six-pair fresh-module shipping protocol before changing default dispatch.
   The current two-pair results select a candidate, not a release decision.

3. **Replace symbolic dispatch and retire redundant strategies.** Exercise
   `HexPolyDetMathlib/{Small,Structural,RowFactor,RatFactor,Tactic}.lean` inputs
   against the new backend. Remove shape selection and duplicate proof assembly
   from production only as those inputs pass correctness, coverage and timing
   gates for both supplied equalities and result-producing forms. A win on a
   supplied equality does not satisfy result-construction coverage. Retain
   mathematical lemmas independently of strategy code. Universal
   boundary cases `n=0,1,2` may remain simple definitions; they need no tuned
   policy. Keep residue/scaling certificate paths only for demonstrated
   uncovered capabilities, not as permanent unmeasured alternatives. Once all
   consumers move, delete unused polynomial frontend/quotation/checker glue and
   its option branches, replacing tests with the new public-path tests.

4. **Implement coefficient adapters.** First confirm the small rational/dyadic
   scaling observations with bounded in-process repetitions and a timing barrier
   for each invocation: the present native measurements are cold single calls.
   Prove the row-scaling determinant equation, positivity/nonzeroness of row
   factors, rational denominator
   divisibility, dyadic shifts and the restoration map. Use the actual normalized
   input, including zeros and negative dyadic precisions. Compare direct and
   scaled methods including discovery, conversion and result normalization.
   Keep direct methods where denominator growth or exponent separation loses.
   Install measured policy regions only after independent dimension and size
   checks. Do not make all fields pass through rational or integer conversion.
   Expose dense univariate arithmetic as an explicit representation option,
   preserving the requested output contract. Include representation conversion
   in any subsequent selection measurement; the current arithmetic comparison
   supplies already represented inputs and establishes no automatic threshold.

5. **Replace the modular hot loop.** Start with one modulus and the existing
   field operations. Implement the fast value loop in C behind `@[extern]`, with
   a Lean logical implementation following the existing repository FFI pattern.
   Pure Lean owned-array/raw-word variants did not close the measured gap; this
   stage does not assume that repackaging them will. Prove the logical model's
   row swaps, row updates, pivot accumulation and singular termination against
   `Matrix.det`. Reuse/refine existing `DetImage`/`Dixon.Echelon` correctness
   instead of duplicating determinant theory. Differential tests check the C
   implementation against the model; they are not a formal proof of the C code.
   Native results never replace kernel-checked proof evidence. Add bounded native
   cross-checks, including singular matrices, swap parity, boundary residues,
   zero multipliers and composite-modulus declines. Only then connect it to the
   existing CRT/divisor producers. Re-measure complete values and either remove
   superseded `Image`/`FlatImage` execution paths or retain the necessary public
   wrappers around the new implementation. Improve prime supply independently;
   do not claim that it solves the elimination gap.

6. **Migrate consumers and finish deletion.** `HexRank/Reduce.lean`,
   `HexGramSchmidt/Int/Core.lean`, and the LLL dependency chain still use Bareiss
   and its algebra: do not delete that library. Modular `Rank`, `Solve`,
   `SolveMat`, `Decomp`, `Divisor` and `Product` share row operations and require
   their own conformance checks after hot-loop changes. `HexDet` policies and
   `HexDetMathlib` carrier correctness must agree on the executed operations.
   Audit names/imports and public umbrellas before removing a shared declaration.
   Retain the reference determinant and independent oracles. Run the appropriate
   full build, kernel/conformance tests, DAG/Phase-4/release-manifest guards and
   fresh proof probes. Publish only through the monorepo release manifest; never
   edit a released mirror directly.

Each production stage is independently reviewable and reversible until its
replacement passes. Remove the losing prototype implementations from production
consideration; keep their archived evidence reproducible. Do not accumulate
every experiment as another permanent dispatch arm.
