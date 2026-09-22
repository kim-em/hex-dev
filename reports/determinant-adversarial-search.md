# Adversarial determinant proof search

The shared-expression prototype loses to Mathlib on algebraically zero entries
and on larger rank-one matrices. Two inputs meet the strongest counterexample
criterion: Mathlib finishes in under a minute while the prototype hits the
60-second fresh-module process ceiling. Unconditional deferred normalization
is therefore not an established replacement architecture.

The prototype is frozen throughout this search: both `Deferred.lean` and
`Arithmetic.lean` have identical recorded hashes in every batch. The comparison
is `shared_bird` against `simp only [norm_det] <;> ring`, including construction
and kernel checking of the supplied-target proof. These are experimental proof
modules, not computational benchmark targets or production dispatch changes.

## Counterexamples

Times below are complete declaration seconds, medians of two observations per
arm in adjacent AB/BA pairs. Both pairs agree on each completed loss. Timeout
rows have just one successful Mathlib observation; the timeout includes module
loading and build overhead and is not a measured 60-second declaration.

| Matrix | Mathlib | Shared prototype |
|---|---:|---:|
| 4×4, algebraically zero entries below the diagonal | 0.264 | 0.333 |
| 6×6, same construction | 0.666 | 4.626 |
| 7×7, same construction | 1.094 | 15.792 |
| 8×8, same construction | 1.535, one sample | 60s process timeout |
| 6×6, scattered algebraically zero entries | 4.407 | 5.107 |
| 7×7, same construction | 14.099 | 19.645 |
| 10×10, rank one | 1.377 | 1.612 |
| 16×16, rank one | 12.320 | 15.015 |
| 20×20, rank one | 39.284, one sample | 60s process timeout |

The zero entries are spelled
`(x + y)^2 - (x^2 + 2*x*y + y^2)`. The triangular construction places them below
the diagonal; the scattered construction places them where `(i + j) % 3 = 0`.
Other entries are sparse polynomials. The target is supplied in expanded form.

The rank-one construction is `A[i,j] = u[i] * v[j]` with independent variables
and supplied target zero. It has no identically-zero input entries. The 20×20
Mathlib process itself took 49.17s, so that baseline is below a minute even when
loading and build overhead are included. No ratio is assigned to the censored
prototype declaration time.

### Controls for spelling and sparsity

Replacing each zero polynomial by literal zero reverses the outcome on the
matched controls. The archived statements are byte-for-byte identical after
that substitution, including the supplied target.

| Control | Mathlib | Shared prototype |
|---|---:|---:|
| 4×4 triangular, literal zeros | 0.234 | 0.155 |
| 6×6 scattered, literal zeros | 4.171 | 3.579 |
| 4×4 dense, zero polynomial added to every nonzero entry | 0.970 | 0.580 |
| 6×6 dense, same addition | 12.882 | 11.918 |

Merely adding cancellation syntax to nonzero entries did not reproduce the
loss. Exposing zeros early permits pruning. The rank-one losses establish that
recognizing zero input entries alone cannot settle the normalization question.

## Other directions searched

The search selected individual cases after inspecting earlier results. It
varied polynomial degree, support, variables, coefficient size, carrier,
dependencies between rows, and the spelling of repeated factors. Representative
completed comparisons and timeout boundaries are below. All completed samples,
ranges and pair outcomes are in the [full inventory](bench-results/determinant-adversarial/inventory.md).

| Direction | Selected case | Mathlib | Shared prototype |
|---|---|---:|---:|
| Higher degree | 4×4, two variables, degree 8 | 5.721 | 2.254 |
| More terms | 4×4, quadratic, six terms per entry | 1.574 | 1.354 |
| More variables | 4×4 quadratic, four variables | 10.385 | 4.249 |
| Independent entries | 5×5, 25 variables | 1.691 | 0.648 |
| Large coefficients | 4×4, up to 512 bits | 1.498 | 0.960 |
| Rational coefficients | 6×6 | 16.663 | 15.799 |
| Characteristic two | 6×6 | 12.644 | 8.882 |
| Composite modulus | 4×4 over `ZMod 6` | 0.531 | 0.376 |
| Dependent row | 6×6, last row sum of first two | 10.168 | 9.942 |
| Skew-symmetric, zero diagonal | 7×7 | 20.491 | 19.859 |
| Repeated expression in entries | 4×4, retained factored expression | 1.552 | 1.242 |
| Common factor | 4×4, factored target | 1.355 | 1.119 |
| Common factor | 4×4, expanded target | 1.881 | 1.513 |
| Vandermonde | 6×6, factored target | 37.381 | 29.399 |
| Circulant | 7×7 | 11.835 | 6.939 |

Mathlib hit the process ceiling on dense 4×4 quadratics in five and six
variables, independent 6×6 entries, the dependent-row 7×7 case, and circulant
8×8. Those batches stopped before running the prototype. Smaller cases were
permitted after timeouts; larger comparable cases were not attempted.

The original ambiguous common-factor example was rerun once unchanged:
Mathlib 0.449s, prototype 0.339s, both pairs favoring the prototype. Its earlier
comparison had conflicting pairs, so it is not a reproducible loss here.
The 4×4 characteristic-two case also has conflicting pairs. Small differences
on dependent-row and skew-symmetric examples should not be treated as robust
advantages from two observations alone.

## What Mathlib does better on the losses

Mathlib's Bird certificate evaluator normalizes entries and arithmetic as it
constructs the recurrence. Its `certEval` derives `isZero` from the normalized
value; the recurrence skips products with zero original entries. The prototype
instead retains raw expressions and reflexivity proofs at entry evaluation,
recognizes only syntactic zero there, and normalizes the shared final expression
and target afterward. See Mathlib's `Mathlib/Tactic/Determinant/Bird/Cert.lean`
and [the prototype](../experiments/Determinant/Deferred.lean).

This saves normalization work on many dense inputs, but also retains an
additional layer of raw intermediate expressions and proofs. Sharing expressions
during proof construction does not ensure cheap term sharing or kernel checking.
The matched zero-spelling controls support the early-pruning explanation.
Rank-one losses suggest intermediate normalization and proof representation
also matter; their exact attribution remains an experiment to do.

A separate profiler diagnostic on the 6×6 triangular matrix with zero
polynomials locates a large cost after the tactic has returned:

| Component | Mathlib, two observations | Shared prototype, two observations |
|---|---:|---:|
| Tactic execution | 0.178–0.202s | 0.421s |
| Share common expressions | 0.068–0.103s | 1.02–1.15s |
| Final type checking | 0.100–0.192s | 1.36–2.36s |

The profiler data is retained in [profiles.json](bench-results/determinant-adversarial/profiles.json).
These instrumented samples are separate from the headline timings, and the
spans are not assumed to be disjoint. An unprofiled tactic-clock diagnostic
also finds roughly 3.14–3.19s outside the prototype tactic versus 0.30–0.31s
for Mathlib. That remainder includes elaboration, term sharing and declaration
processing as well as kernel checking; it is not itself a kernel measurement.

The next general comparison should use Mathlib's normalized Bird certificate
evaluator while keeping a common scalar/atom context through the supplied-target
comparison, avoiding the cleanup and re-elaboration boundary. Compare that with
general early normalization in the deferred prototype, on these losses and on
the dense and Vandermonde winning controls. This directly tests normalization
policy and proof representation without adding triangular or rank-one dispatch
strategies. Neither proposed improvement has been measured here. The
[replacement proposal](determinant-redesign-proposal.md) now makes this decision
an experimental prerequisite to migrating the symbolic backend.

## Protocol, validation and limits

The [runner](../experiments/Determinant/adversarial.py) uses fresh `lake build`
proof modules and the existing shared-host CPU lease. Each complete ordinary
batch has two adjacent pairs in AB/BA order, with Mathlib first. The synchronous
declaration clock includes statement elaboration, proof construction, auxiliary
checks and final kernel checking. Import loading, parsing and independent target
generation are outside that clock. Both arms receive the same statement and
imports. Targets use independent subset expansion with FLINT, except known-zero
rank-one targets; both Lean arms still check the claimed identity.

Every invocation has a 60-second process ceiling. The runner serializes use of
the worktree, limits individual batches to six minutes, stops on failure, and
refuses coordinatewise larger cases in a timed-out family with the same carrier
and representation. It caps the cumulative search allowance at 40 minutes and
requires remaining allowance for four full invocation ceilings before starting
a case. No memory cap, background service, automatic grid, quiet-host waiting
or sample-discard rule is used.

The archive contains 52 batches: 43 complete, five Mathlib timeouts, two
prototype timeouts after a successful Mathlib baseline, and two harness errors.
This count includes controls and diagnostics, not 52 independent mathematical
matrices. All 174 successfully checked result theorems have an exact-name axiom
audit; dependencies are limited to `propext`, `Classical.choice`, and `Quot.sound`.
New measurement batches total 2085.6s (34m46s); including the prior redesign's
557.8s gives about 44m03s of retained measurement time.

Both harness errors are retained: a trailing `ring` after `norm_det` had closed
the goal, corrected by `<;>` sequencing, and an invalid profiler-option helper,
corrected before the diagnostic ran. The successful profiler batch's original
per-sample kernel arrays were empty because the parser missed grouped multiline
messages. The report parser recovers the spans from retained compiler output;
it does not replace observations or rerun them. Source snapshots preserve the
runner version used by each batch.

[Guard validation](bench-results/determinant-adversarial/validation/guards-and-controls.json)
checks timeout refusal in six families, cumulative allowance refusal, exact
zero-spelling controls, and equivalence of the optimized rank-one target
generator with earlier statements. The separate serial-guard record verifies
that a second runner is refused before launching a proof. The inventory generator
rechecks theorem axioms and frozen prototype hashes.

This is a bounded adversarial search, not the six-pair production qualification
protocol or an exhaustive survey. It does not exhaust seeds, matrix structures,
rings, or interactions between parameters. Changing coefficient size or variable
count can also change random support choices, so those comparisons do not isolate
a single causal variable. There are still plausible untested directions. The
concrete counterexamples already disprove general superiority of the frozen
prototype and provide a demanding comparison set for its replacement.
