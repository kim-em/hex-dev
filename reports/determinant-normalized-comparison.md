# Normalized determinant proof comparison

Reusing Mathlib's normalized Bird certificate evaluator and checking the target
in the same atom context removes the large cancellation losses of the deferred
prototype. It also wins the dense quadratic and factored Vandermonde controls.
Returning that certificate directly for an already-normal target also wins
the 16×16 rank-one comparison: 25.39s versus Mathlib's 31.37s. However, the
10×10 rank-one case still favors Mathlib, 4.35s versus 4.55s. Coverage of this
last assembly variant is narrow; this is not universal superiority.

## Construction

[Normalized.lean](../experiments/Determinant/Normalized.lean) extracts a literal
matrix, applies the universal Bird correctness theorem, and calls Mathlib's
`certBirdDet`. It calls `certEval` on the supplied target within the same
`CertM`/`AtomM` run, compares the resulting normal forms, and composes their
proofs. It does not call `norm_det`, `eval_det`, or a determinant fallback.

This avoids the simplifier's cleanup of the determinant normal form followed
by a separate `ring` normalization of that expression and the target. Entries
and intermediate arithmetic still normalize eagerly, as in Mathlib. The scalar
cache uses `Common.mkCache`, including available field and characteristic
instances; this is necessary to compare rational coefficients directly rather
than leave their denominators as unrelated atoms.

Three manual entry points vary only general proof assembly:

- `normalized_bird`: explicit symmetry and transitivity applications.
- `composed_bird`: Lean's `mkEqSymm` and `mkEqTrans`, which remove syntactic
  reflexivity applications.
- `direct_bird`: the same constructors, plus returning the determinant
  certificate immediately when its normal form is definitionally equal to the
  target. This avoids normalizing and composing a proof of an already-normal
  target.

These variants contain no matrix-family tests. They remain experimental, with
no production dispatch or normative SPEC changes.

## Normalized evaluator with explicit assembly

Each row is a fresh comparison with `simp only [norm_det] <;> ring`, using two
adjacent AB/BA pairs. Times are complete declaration seconds, including all
kernel checks. Both pairs agree on the direction of every row; small differences
still warrant caution with only two observations per arm.

| Input | Mathlib | Normalized frontend |
|---|---:|---:|
| 4×4, cancellation expressions below the diagonal | 0.259 | 0.171 |
| 6×6, same construction | 0.672 | 0.516 |
| 8×8, same construction | 1.630 | 1.065 |
| 7×7, scattered cancellation zeros | 14.941 | 14.469 |
| 4×4, dense quadratic entries | 0.710 | 0.531 |
| 5×5 Vandermonde, factored target | 1.385 | 0.533 |
| 10×10 rank one | 1.425 | 1.445 |
| 16×16 rank one | 14.332 | 16.251 |

Cancellation zeros are `(x+y)^2 - (x^2 + 2*x*y + y^2)`. Rank-one entries are
`u[i] * v[j]`, with no identically-zero input entries and supplied target zero.
The statements match the corresponding [adversarial inputs](determinant-adversarial-search.md).
The old deferred prototype timed out on the 8×8 cancellation case. That is
historical context, not an adjacent before/after timing ratio: this round's
Mathlib baseline was measured afresh.

The [normalized inventory](bench-results/determinant-normalized/inventory.md)
contains ranges, sources and raw observations. These eight cases do not replace
the broader adversarial corpus or establish performance on every retained loss.

## Assembly experiments

Using Lean's equality constructors alone leaves a small rank-one loss at 10×10:
Mathlib 1.401s, composed frontend 1.416s, both pairs agreeing. The corresponding
normalization proof for a zero target uses `Ring.cast_zero`, not a syntactic
`Eq.refl`, so syntactic reflexivity elimination alone does not remove that target
comparison. See `Ring.evalCast` in Mathlib's `Mathlib/Tactic/Ring/Basic.lean`.

A separate kernel-profile diagnostic reverses that timing order: Mathlib
2.94–4.22s, composed frontend 1.52–2.23s. Its final type-checking spans are
1.01–1.53s and 0.642–0.761s respectively. This diagnostic does not reproduce the
ordinary timing loss and cannot establish its cause. It is retained separately
in the [composed archive](bench-results/determinant-composed/inventory.md);
neither these samples nor their component times are pooled with ordinary runs.

The direct-conversion variant has the following separate, unprofiled comparisons:

| Input | Mathlib | Direct target conversion |
|---|---:|---:|
| 4×4, dense quadratic entries | 2.055 | 1.574 |
| 10×10 rank one | 4.352 | 4.549 |
| 16×16 rank one | 31.366 | 25.390 |

Both pairs favor direct conversion on the dense and 16×16 rows, and both favor
Mathlib on the 10×10 row. In particular, the 16×16
comparison is a roughly 19% win against its adjacent Mathlib baseline, despite
the earlier explicitly composed frontend losing on this same mathematical input.
Absolute times differ substantially between stages. Do not compare their raw
times as if the stages were adjacent arms, or transfer the normalized frontend's
broader coverage automatically to the direct-conversion variant.

## Design consequence

The useful change is to keep normalized certificates through the supplied-target
comparison and avoid unnecessary proof composition. Unconditional deferral has
no demonstrated need as the production default. Direct reuse of Mathlib's core
evaluator is a viable general candidate; there is no reason to duplicate its
recurrence merely to avoid calling the `norm_det` tactic.

The 10×10 rank-one input remains a concrete counterexample for the newest
variant: the prototype is about 4.5% slower, well within a minute. Its small but
consistent loss needs an unprofiled comparison of emitted proof structure and
frontend work; the profile diagnostic above cannot establish its cause.

The next comparison set should also carry the direct-conversion frontend across the
remaining retained adversarial inputs, especially scattered zeros, factored
targets, rational coefficients, positive characteristic and the 20×20 rank-one
case. Those cases are not all measured for the final variant here. Result
construction without a supplied target and alternative determinant schedules
also remain open. The two-pair exploratory protocol does not authorize a
default-dispatch decision or a production migration.

## Protocol and validation

The runner selects one case at a time and stops a batch on any failure or
timeout. All variants use fresh modules with identical imports between arms,
the existing automatic CPU lease, and synchronous declaration clocks. Statements
and generated targets are outside the declaration clock; every proof and final
kernel check is inside it. Host observations and every completed sample are
retained without a quiet-host condition or sample rejection.

The normalization variants share one ten-minute measurement allowance across
sibling output roots. A different variant cannot reset that allowance. The
default invocation ceiling is 60 seconds; the 16×16 direct comparison
uses 55 seconds, and the final 10×10 direct comparison uses 15 seconds, to reserve
all four invocations within the remaining allowance. These are process ceilings,
including module loading and build overhead. They are not exact tactic-time bounds. No memory cap or
background monitoring service is used.

All thirteen batches completed, giving 52 checked proof samples, including four
from the separate profiler diagnostic. Their total wall time is 584.4s (9m44s),
within the ten-minute allowance. Including the earlier redesign and adversarial
search gives about 53m48s of retained measurement time. No failed or timed-out
proof sample was removed; this round had none.

Each stage archives the exact prototype and runner sources. The prototype is
frozen within each variant's measured stage; later assembly changes are not
substituted into the earlier archive. The old deferred prototype remains
unchanged. Variants were compared with adjacent Mathlib baselines, not directly
with each other, so differences between their separate batches do not provide
an isolated causal estimate for assembly changes.

`lake build Determinant.NormalizedAudit` checks generic commutative rings,
reordered targets, algebraic cancellation, rational coefficients, composite
modulus, singleton matrices, direct zero targets and rejection of false targets.
The final audit has twelve accepted theorems and four rejection checks. All
accepted theorem dependencies are limited to `propext`, `Classical.choice` and
`Quot.sound`; every measured result theorem is also audited by exact name.
The [combined-budget guard check](bench-results/determinant-normalized/validation/combined-budget.json)
verifies refusal before launching a proof when the earlier variants consume the
remaining allowance. The [input and budget checks](bench-results/determinant-direct/validation/inputs-and-budget.json)
also verify exact equality with twelve archived ordinary input statements and
the final three-variant allowance. Reproduction commands are in the
[experiment README](../experiments/Determinant/README.md#normalized-determinant-comparison).
