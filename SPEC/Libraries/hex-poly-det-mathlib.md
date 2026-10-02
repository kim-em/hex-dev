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
A simproc returns no rewrite on a recoverable capability/work-budget decline,
with a trace reason; malformed proofs and internal errors are failures and
propagate.

## Programmatic interface and syntax ownership

In `HexMatrixMathlib.Det`, expose `compute (cfg : Config) (A : Expr) :
MetaM (Outcome Result)`, where the new `Result` contains `value : Expr` and
`proof : Expr` proving `Matrix.det A = value`. Expose
`certified (A : Expr) (cfg : Config := {}) : MetaM (Outcome Expr)`
as the record adapter, preserving existing calls with just `A`. The numeric
internal `Proof`, whose additional fields include the checker and row list,
remains separate; the common `Result` has only `value` and `proof`. Keep internal
atom-indexed certificates private to the evaluation session. These expression-level APIs are Meta APIs,
not new trusted operations. The numeric owner provides the dispatcher and numeric
implementation; the companion registers the symbolic implementation through one
extension hook. There is one programmatic operation, not two competing functions
selected by import order.

Declare the argument-taking tactic as `&"det" optConfig colGt term:max
" with " ident ident : tactic`, on its own named syntax kind in the existing
syntax owner. This preserves the bare tactic and avoids consuming the next
indented tactic as a matrix argument. Register a final diagnostic for this kind
as for the equality form. Trace routes, limits and declines through the existing
`HexMatrix.certificate` class. Document every `Config` field's units and route;
non-default symbolic limits are accepted without a warning on numeric input and
have no effect there, while `packing` has no effect on symbolic input.

## Inputs and mathematical scope

Accept square `Matrix (Fin n) (Fin n) R` literals with a known dimension and a
`CommRing R` instance. Reuse the shared literal recognizer for `!![...]`,
`Matrix.of ![...]`, `fun i j => ...`, and `Matrix.ofArray xs h`, including
its bounded unfolding through definitions. Support local variables and
parameters, empty and singleton matrices. Symbolic identification must not use
`decide (entriesEq ...)` or require `DecidableEq R`: identify the literal with
its row-major entries using the `List.ofFn` definitional transport used by
Mathlib's determinant normalizer, or finite extensionality composed with proved
entry equalities when unfolding/simplification requires it. This applies to all
four input syntaxes. Unresolved matrix/type metavariables are not guessed.

Scalar arithmetic uses the supported Mathlib ring normalization operations:
constants, addition, subtraction, negation, multiplication and natural powers.
Other expressions may be opaque atoms. Targets may introduce additional atoms;
identities such as `d + y - y` must not be rejected merely because `y` is absent
from the matrix. Preserve the ring normalizer's supported natural-exponent
identities rather than imposing the old fixed-exponent reflection grammar.
Unrecognized operation instances are not replaced by familiar ones syntactically.

Generic commutative rings and rational coefficients use proved scalar operations.
Characteristic-specific coefficient identities must also be preserved. When a
positive literal characteristic is recognized for the carrier (including `ZMod`
and polynomial carriers) or supplied by a local `CharP R p` instance with `p`
reducing to a positive numeral, use proved coefficient reduction modulo that
characteristic. Reuse Mathlib's
`ReduceModChar` machinery or its lemmas as a scalar operation, without restoring
a residue determinant strategy. Reduce coefficients when finalizing a public
value and on both sides of equality comparison, then combine like terms with
the scalar normalizer. A known characteristic zero performs no modular pass;
an unknown characteristic retains characteristic-independent normalization.
For example, retain `a*b = a*b + 3*a*b` over `ZMod 3` and a determinant whose
integer normal form is `-2*x^3` but whose value is zero over `ZMod 2`. Test
composite characteristic and an explicit generic `CharP R p` instance too.
Do not claim completeness for arbitrary finite-ring identities. Field-specific
transformations require the corresponding instances. Symbolic division is total, including zero
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
The pinned scalar evaluator has no division-policy hook. A narrowly scoped,
licensed adaptation of its traversal is permitted for coefficient/quotient
policy while reusing Mathlib's arithmetic and proof operations. Preserve author
headers, record the upstream revision, and maintain one policy-driven adapter,
not separate historical evaluator copies. On every Mathlib pin change, run the
scalar, characteristic, rollback and determinant regression tests. An upstream
hook is desirable but not a prerequisite for the Hex implementation.

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
complete-call cost. Inline the direct algebraic proof into its surrounding
declaration; do not seal every intermediate result in an auxiliary theorem or redundantly precheck
it in Meta. The kernel validates the complete declaration. Consequently an
invalid generated proof can be reported at declaration checking rather than
inside the tactic invocation; there is no promise of synchronous tactic-time
kernel rejection for this path. Such rejection remains a hard failure.

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
Use Lean's public heartbeat units (one unit is 1,000 internal heartbeats).
This is an additional ceiling, never an increase to the caller's remaining
allowance: with Lean's smaller ambient default, the ambient limit binds first.
Zero configuration limits are rejected intentionally; unlike the ambient Lean
option, zero does not disable these local safeguards.

Recoverable work-budget exhaustion is a structured decline. Runtime heartbeat
or recursion-depth exceptions, whether ambient or from the local ceiling,
propagate unchanged; neither the simproc nor speculative normalization swallows
them as algebraic refusal or turns them into no-progress success. Trace the
selected ceiling before entering the session so a runtime message has context.
Goal restoration applies to ordinary comparison/capability declines; resource
exceptions retain Lean's normal transactional behavior. Use normal trace classes
rather than global options for diagnostics; term/simproc calls use the same defaults.

Select numeric determinant computation whenever the matrix is a recognized
closed integer/rational input. For result forms, delegate to that evaluator
before symbolic work. For equality goals, whole-tactic delegation is allowed
only when the numeric closing handler accepts the complete goal. Otherwise the
companion obtains the numeric certified value and uses the shared scalar target
comparison; it does not compute that numeric determinant with Bird or leave a
simp-only residual goal. In particular, `(!![1,2;3,4] : Matrix _ _ Int).det =
x - x - 2` must close with the companion imported. Preserve
`notApplicable`, `declined`, `success` and internal failure distinctions:

- An unrecognized matrix, operation, unresolved input or missing commutative-ring
  structure is not applicable and may delegate to another Hex handler.
- An accepted input whose scalar comparison cannot close or whose recoverable
  work budget is exhausted is a decline.
  Name the stage, exhausted budget and count/limit when available; do not try a
  different determinant algorithm afterward.
- Success returns a value and an equality proof, or closes the supplied equality.
- An invariant violation detected in Meta, or an emitted proof rejected when
  its declaration is checked, is a failure, never a decline hidden by another
  handler. Preserve `no_fallback` behavior for tactic handlers.

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
checks. Remove determinant-specific packed/tree wrappers and residue frontend
transport with no independent consumers; preserve the plain `opsMod` checker
soundness theorem in `Residue.lean` separately from that transport; do not delete
reusable algebra or a shared checker just because one tactic stops using it.
Separate retained computational soundness imports from the symbolic tactic's
imports. The full companion retains `HexReflect`/`HexReflectMathlib` while its
plain integer/residue soundness imports require them; that is not a symbolic
frontend dependency. Required registry dependencies after cleanup are
`HexPolyDet: [HexBareiss, HexMvGcd, HexDeterminant, HexMatrix, HexBasic]` and
`HexPolyDetMathlib: [HexPolyDet, HexBareissMathlib, HexReflect,
HexReflectMathlib, HexMvPolyMathlib, HexMatrixMathlib]`, with their transitive
closure. Drop both determinant libraries' direct Kronecker dependencies.
The symbolic tactic module imports the numeric owner, literal layer and Mathlib
proof machinery, not the retained native soundness module. Update umbrellas,
library dependency registrations, probes and documentation to match the resulting source.

Production must not import `experiments/Determinant`. Retire superseded
experimental proof backends from active builds once their tests are migrated.
Preserve recorded source snapshots and revision-based reproduction of historical
measurements. Native-value experiments are outside this symbolic replacement.

### Cleanup inventory

| Surface | Disposition |
|---|---|
| `HexPolyDetMathlib/Tactic.lean`, `Frontend.lean` | Replace with the shared evaluation/session interface and public handlers; remove legacy dispatch and witness assembly. |
| `Small.lean`, `Structural.lean`, `RowFactor.lean`, `RatFactor.lean`, `Certificate.lean`, legacy `Normalize.lean` | Remove their determinant strategies; migrate mathematical regression cases. |
| `Packed.lean`, `Tree.lean`, legacy `Scaling.lean` | Remove determinant-only encodings and transport; preserve independently used lemmas in their owning modules if any. |
| `Sound.lean`, `Residue.lean` | Retain native producer/plain-check soundness, including `opsMod` soundness; remove frontend identification, target reconstruction and unused reflection transport separately. |
| `HexPolyDet/Basic.lean` | Retain native values, witnesses, budgets, canonical conversion and plain checker operations. |
| `HexPolyDet/Packed.lean`, `Select.lean`, `PackedTests.lean`; `bench/HexPolyDet/PackedBench.lean` | Remove obsolete determinant packed APIs/tests/driver and the `hex_poly_det_packed` Lake target. |
| `scripts/bench/det_packed_*`, `det_residue_sweep.py`, `det_structural_sweep.py` | Retire route-specific runners, generated manifests and selection tests; keep historical reports and raw data. |
| `det_symbolic_*`, `det_ring_solver_*`, `test_det_declines.py`, `det_bench_limits.py` and its tests | Consolidate into the general symbolic proof/result runner and diagnostics; preserve serial admission and timeout guards. |
| `det_tactic_*` runners | Retain independent numeric certificate measurements and scope controls. |
| `bench/HexPolyDetMathlib/ProofProbe`, including `RingSolver*` | Replace retired route-specific probes with the focused general evaluator corpus; preserve source snapshots of measured old probes in reports/revisions. |
| `.github/workflows/ci.yml`, Lake targets and `libraries.yml` | Update the existing job's detector tests/probe invocations, library entries, umbrella imports and retired executable targets; add no jobs/workflows. |
| `scripts/bench/proof_only_runtime_exemptions/issue-10236-*` | Retain provenance for the preserved generic Bareiss checker; update descriptions/references only where consumers changed, rather than deleting generic-certificate evidence. |
| `DeterminantExperiment` and historical proof tactic variants | Remove superseded active proof targets/imports after tests migrate; keep native-value experiments and revision-based evidence reproduction. |

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
