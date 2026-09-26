# hex-poly-det-mathlib

Proof-producing evaluation of symbolic determinants of Mathlib matrix literals.
Use one cached, division-free Bird recurrence over the user's commutative ring,
with compact scalar equality proofs. Compute a determinant expression and prove
it correct without requiring the caller to supply its value. Equality goals add
a comparison with the requested expression to the same evaluation session.

The library extends the determinant syntax owned by hex-bareiss-mathlib. Closed
integer and rational inputs retain that library's numeric certificate backend.
Native polynomial values and checked polynomial witnesses remain the separate
[hex-poly-det](hex-poly-det.md) operations. They are not prerequisites of the
symbolic proof evaluator. There is no matrix-family strategy dispatcher and no
implicit invocation of Mathlib's `norm_det` or `eval_det`.

## Public interface

Importing `HexPolyDetMathlib` enables the symbolic handlers. The syntax owner
remains hex-bareiss-mathlib; extensions attach to its syntax kinds instead of
redeclaring keywords. Preserve the existing numeric forms.

| Form | Contract |
|---|---|
| `det` | Close `A.det = e` or `e = A.det`; compute the determinant, compare with `e`, and compose the equality, using symmetry when necessary. |
| `det A with d hd` | Compute without an expected answer; introduce a local definition `d : R` containing the computed value and `hd : A.det = d`, then leave the surrounding goal available. Both names are explicit. |
| `det% A` | Elaborate to `HexMatrixMathlib.Certified Matrix.det A`, with `value : R` and `proof : A.det = value`. No expected determinant value is needed. |
| `simp only [Hex.normPolyDet]` | Explicitly rewrite supported determinant occurrences to their computed values, including nested occurrences and hypotheses selected with `at`. |
| `Hex.norm_det` | Keep hex-bareiss-mathlib's numeric certificate simproc. |

For example, the result may be used without predicting its expression:

```lean
let r := det% A
have h : A.det = r.value := r.proof
```

The result-introducing tactic offers the same operation without manually
projecting the record:

```lean
det A with d hd
-- d is a local definition; hd : A.det = d
```

Both tactic forms accept `optConfig` before the matrix argument, if any. Term
and simproc forms use default configuration. The programmatic evaluator accepts
an explicit configuration and returns the same value/proof contract. Neither
result-producing form calls the equality tactic with an invented right-hand
side or computes the determinant twice. Introduced names follow Lean's ordinary
local-name hygiene. Numeric notation retains the syntax owner's integer default;
explicit annotations and expected record types must not be overridden.

Bare `det` is a closing tactic. If comparison declines, restore the original
goal and metavariable state. It does not leave an unexplained residual equality.
The result-introducing form does not solve or otherwise change the ambient goal.
A simproc returns no rewrite on a capability/budget decline, with a trace reason;
malformed proofs and internal errors are failures and propagate.

## Inputs and mathematical scope

Accept square `Matrix (Fin n) (Fin n) R` literals with a known dimension and a
`CommRing R` instance. Reuse the shared literal recognizer for `!![...]`,
`Matrix.of ![...]`, `fun i j => ...`, and `Matrix.ofArray xs h`, including
its bounded unfolding through definitions. Support local variables and
parameters, empty and singleton matrices, and the recognizer's existing
identification proofs. Unresolved matrix/type metavariables are not guessed.

Scalar arithmetic uses the supported Mathlib ring normalization operations:
constants, addition, subtraction, negation, multiplication and natural powers.
Other expressions may be opaque atoms. Targets may introduce additional atoms;
identities such as `d + y - y` must not be rejected merely because `y` is absent
from the matrix. Preserve the ring normalizer's supported natural-exponent
identities rather than imposing the old fixed-exponent reflection grammar.
Unrecognized operation instances are not replaced by familiar ones syntactically.

Generic commutative rings, rational coefficients and positive characteristic
are supported through proved scalar operations. Field-specific transformations
require the corresponding instances. Symbolic division is total, including zero
denominators: never cancel a factor with its inverse without a proof. No domain,
characteristic-zero or nonzero-pivot assumption is imposed on generic matrices.

This is not a complete field simplifier or a hypothesis solver. Expressions may
remain opaque; identities requiring relations between atoms or local hypotheses
may decline. Unequal symbolic normal forms mean the comparison did not close,
not that the mathematical proposition has been proved false. A genuinely closed
numeric mismatch may report the computed value and the unequal supplied value.

## Evaluation and proof construction

Use Mathlib's universally proved Bird determinant recurrence. Cache original
entry certificates, intermediate entry certificates and diagonal sums. Preserve
zero pruning based on proved normalized zeros. Dimension-zero and singleton
behavior are recurrence boundary cases, not alternative determinant strategies.

Each scalar result contains its subject, normalized expression and a proof of
their equality. Addition, multiplication and negation use direct applications of
small congruence lemmas rather than chains of equality manipulation. Reuse
existing Mathlib lemmas when their instances fit; keep any necessary adapters
small and test their elaboration and kernel costs. Combined recurrence equations
may reduce repeated unfolding without changing the algorithm or bypassing cache
insertion. Do not copy an entire arithmetic library to change these constructors.

The determinant computation is independent of any supplied target. Its internal
certificate and scalar context can then be consumed in either of two ways:

- Result production cleans internal coefficient notation into an ordinary Lean
  expression and returns that expression with `A.det = value`.
- Equality proving first attempts cheap conversion at reducible transparency,
  then normalizes and compares the target in the same atom context. It avoids
  constructing and cleaning an intermediate public result unnecessarily.

Do not perform unrestricted definitional equality through concrete ring
implementations. Do not rerun the determinant during target comparison. Apply
matrix identification and the universal correctness theorem by bounded proof
assembly; avoid Meta unification that repeatedly unfolds large literal matrices.
All input-dependent checking, including auxiliary declarations, belongs to the
complete-call cost. Direct algebraic proofs need not be forced through a separate
closed certificate checker or redundantly prechecked in Meta.

A public value is the evaluator's normal form, not necessarily a factorization,
a common-denominator rational function, or a fully expanded polynomial. Numeric
results are ordinary normalized integer/rational values. The symbolic value
must be readable Lean syntax without internal raw coefficient constructors.
Do not promise a stable printed monomial order. Fully expanded output and native
value-only execution are separate operations, not implicit work in `det%`.

## Scalar policy and quotient relations

Use one explicit scalar policy with narrow internal operations, not positional
Boolean switches selecting historical experiments. Normalize numeric denominators
as coefficients. Retain symbolic quotients as compact atoms until selected
multiplicative relations warrant expansion.

Factor signatures record multiplicative factors, inverse factors and natural
exponents. They ignore scalar coefficients and select possible collisions only;
they are never evidence of equality. Expand selected products using existing
proved scalar normalization and arithmetic. A false collision may waste work but
cannot establish a false equation. Missed collisions may cause a later comparison
to decline. The parser is conservative for unsupported syntax.

Cache factor signatures and expansion proofs. Store sum-tail indices in
persistent trie maps/sets so adjacent tails share branches instead of copying
bucket arrays. Skip collision search when each compact atom has a private factor,
a sufficient injectivity test. Invalidate that verdict when the atom table grows.
Normalize entries before inserting them into the recurrence cache, so newly
proved zeros permit ordinary zero pruning.

Use joint signature comparison to align determinant and target representations,
with separate selections for each side. Preserve an unmodified sum tail when
its selections are exhausted. Bound speculative expansion and restore both Meta
and atom state after a refusal. Relation hooks must run outside speculative
regions; cached certificates require a stable atom-table prefix. Keep all such
caches scoped to one evaluation session and test the rollback boundary.

If compact comparison fails, permit one stronger scalar comparison. Re-normalize
both expressions in a fresh atom context; only expressions and equality proofs
cross that boundary, never old atom indices. This is scalar normalization, not
a determinant fallback, and consumes the same remaining call budget.

## Configuration, outcomes and checking

The syntax owner provides `HexMatrixMathlib.Det.Config` extending
`HexMatrixMathlib.KernelConfig`. Preserve `packing := true` and `det -packing`
for the numeric backend. Packing has no effect on direct symbolic proofs; route
traces make that distinction visible. Add `maxHeartbeats := 2000000` and
`maxRelationWork := 1000000`. Relation work counts distinct indexed sum tails;
it does not claim to bound all scalar arithmetic. The heartbeat ceiling covers
the symbolic evaluation session, including result cleanup or target comparison.
Never increase the caller's remaining heartbeat allowance. Zero limits are
explicit rejection, not a way to disable bounds. Use normal trace classes rather
than global options for diagnostics; term/simproc calls use the same defaults.

Recognize and delegate closed numeric inputs before symbolic work. Preserve
`notApplicable`, `declined`, `success` and internal failure distinctions:

- An unrecognized matrix, operation, unresolved input or missing commutative-ring
  structure is not applicable and may delegate to another Hex handler.
- An accepted input whose normalization or budget cannot finish is a decline.
  Name the stage, exhausted budget and count/limit when available; do not try a
  different determinant algorithm afterward.
- Success returns a value and an equality proof, or closes the supplied equality.
- An invalid emitted proof or invariant violation is a failure, never a decline
  hidden by another handler. Preserve `no_fallback` behavior for tactic handlers.

Trace the selected numeric-certificate or symbolic-Bird route and any decline.
Diagnostic relation counters include target alignment and are emitted after
comparison. Expensive profiling/node inspection is separate from ordinary calls.

Accepted proofs depend on `propext`, `Classical.choice` and `Quot.sound` only.
No `sorry`, added axiom, `native_decide` or native execution substitutes for proof
checking. Computational libraries stay Mathlib-free; this companion may reuse
Mathlib's evaluator and proof theorems.

## Implementation boundary and deletion

The symbolic frontend depends on the shared literal layer, the numeric syntax
owner and Mathlib's Bird/ring machinery. It must not require polynomial witness
production, packed determinant selection, reflection quotation or residue
certificate preparation to prove a symbolic determinant.

Remove the symbolic triangular/zero recognizer, small closed formulas, sparse
cofactor strategy, row-factor and rational-factor dispatch, and the old
polynomial-certificate fallback. Remove their determinant-specific quotation,
selection, reconstruction, options and tests whose only purpose is the retired
implementation. Transfer mathematical regression cases to the general evaluator.

Retain native `polyDet`, polynomial witness/check APIs and their required
soundness theory, the numeric certificate backend, and shared Kronecker product
checks. Remove determinant-specific packed/tree/residue wrappers with no
independent consumers; do not delete reusable algebra or a shared checker just
because one tactic stops using it. Separate retained computational soundness
imports from the symbolic tactic's imports. Update umbrellas, library dependency
registrations, probes and documentation to match the resulting source.

Production must not import `experiments/Determinant`. Retire superseded
experimental proof backends from active builds once their tests are migrated.
Preserve recorded source snapshots and revision-based reproduction of historical
measurements. Native-value experiments are outside this symbolic replacement.

## Native polynomial witness soundness

Retain `Hex.PolyDet.check_of_ok`, `produce_check` and the plain polynomial
checker soundness needed by the native witness APIs, with their actual
coefficient-domain and representation assumptions. A passing plain check proves
the denoted polynomial matrix's determinant equals the denoted witness value.
Triangular witnesses use nonzero transform diagonals; singular witnesses use a
nonzero kernel vector. The producer theorems establish successful-check behavior,
not that production always succeeds within a budget. These theorems are separate
from the symbolic evaluator and do not require the retired packed selection or
matrix-family strategies.

## Verification and shipping

Test all public forms, both equality orientations, the four literal syntaxes,
local parameters, inferred/annotated carriers, empty/singleton inputs, concrete
integers/rationals, generic rings, characteristic two and composite characteristic.
Include additional target atoms, supported variable exponents, zero denominators,
nested quotient spelling, false targets, unsupported operations, metavariable
preservation and exact budget diagnostics. Test target-driven atom-table growth,
cache insertion/reuse, entry-zero pruning and speculative rollback. Audit accepted
theorems' axioms and assert the selected route without invoking Mathlib tactics.

For result forms, compute before constructing any independent reference answer;
then check the value and its equality proof. Include nonzero symbolic outputs
and numeric outputs, and consumption via projections and the introduced locals.
A supplied-target success does not establish result-producing coverage.

Run `lake build`, the relevant kernel/conformance targets,
`scripts/check_dag.py`, `scripts/check_phase4.py`, and
`scripts/release/check_released_manifest.py`. Extend existing CI scripts rather
than adding jobs. Runtime benchmarks remain Mathlib-free; proof probes are manual
fresh-module comparisons, not native value benchmarks.

Use six adjacent pairs in alternating AB/BA order with import-only baselines
and retained samples on one automatically leased CPU. Compare equality proving
with the unmodified pinned `norm_det` followed by `ring`; compare result
production with Mathlib determinant normalization without providing either arm
an answer. Include output cleanup and every kernel/auxiliary check. Keep tracing,
axiom inspection and profiling outside ordinary samples.

The focused equality corpus contains the original quadratic 4×4 issue fixture,
rank-one 10×10, independent quotients with a dependent row at 6×6, product
denominators at 5×5, identity plus rank one at 5×5, two-term and degree-eight
quotient numerators at 4×4, a dense generic-ring 4×4 and a small composite-
characteristic control. Add numeric-backend regression controls. For result
production start with nonzero numeric and symbolic 2×2/3×3 outputs, then the
quadratic 4×4 and identity-plus-rank-one 4×4 cases. These are coverage directions,
not new dispatch predicates.

Run smaller cases first, serially, with a 60-second process ceiling and a
30-minute aggregate measurement ceiling including failures and diagnostics.
Stop larger comparable cases after a timeout; retain partial batches and do not
count them as six-pair results. Permit at most one unchanged rerun of an
inconclusive case within that same allowance. No broad grid or unrelated-library
performance run is required. Profile only an unexpected result or the required
representative attribution; do not reset the allowance to finish a sweep.

Publish observed gains, ties, losses, declines and unmeasured cases with their
source revisions. Explicit `det`, result tactics and terms, and opt-in
`Hex.normPolyDet` may ship with documented losses. Do not put this evaluator in
a default simp chain or introduce matrix-family selection to conceal those
losses. Universal superiority and further Bird/Bareiss/Berkowitz experiments
are not conditions of this explicit-interface release.
