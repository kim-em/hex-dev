# Transferable determinant improvements for Mathlib

The symbolic determinant design reuses Mathlib's division-free Bird recurrence,
its correctness theorem and its proof-producing ring arithmetic. The useful
upstream contributions are small improvements to that machinery, not a competing
copy of `norm_det` or the Hex numeric certificate implementation.

The reference Mathlib revision is `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The retained Hex experiment is
[`dccd276f7`](https://github.com/kim-em/hex-dev/tree/dccd276f7/experiments/Determinant),
with [controlled evidence](https://github.com/kim-em/hex-dev/blob/dccd276f7/reports/determinant-goal-investigation.md)
and the [quotient-relations report](https://github.com/kim-em/hex-dev/blob/dccd276f7/reports/determinant-relations.md).
Its final persistent-cache and diagnostic corrections have correctness validation
but no new performance measurements. Two-pair observations below select proposals;
they are not universal performance guarantees or six-pair shipping evidence.

## Candidate PRs

| Order | Change | Likely location | Readiness |
|---|---|---|---|
| 1 | Smaller scalar congruence proofs | `Mathlib/Tactic/Determinant/Bird/Cert.lean`, using `Ring.Common` lemmas | Small, supported by a controlled comparison |
| 2 | Reusable expression-and-proof evaluation and supplied-target comparison | `Mathlib/Tactic/NormDet.lean` and Bird evaluator interface | API proposal; target-free evaluation already exists internally |
| 3 | Explicit scalar-normalization policy hook | `Mathlib/Tactic/Ring/Basic.lean` and Bird certificate construction | Needs API discussion and unchanged-default regressions |
| 4 | Selective quotient relations and bounded speculation | Scalar evaluator extension using the hook | More experimental; validate complexity and remaining losses first |
| 5 | Combined recurrence equations | Bird certificate lemmas | Smaller proof structure; extra time improvement unestablished |

## Compact congruence proofs

`certAdd`, `certMul` and `certNeg` construct a proof that an operation on the
original subjects equals the operation's normalized result. Replace chains of
`congrArg`, `congr` and `Eq.trans` with one application of a suitable congruence
lemma. `Ring.Common` already has closely related lemmas. Check the ring/semiring
instance parameters before choosing direct reuse or a small adapter; the
experiment's duplicate statements are not a recommendation to add duplicates.

The controlled 10×10 rank-one comparison changes only these proof constructors:
complete declaration medians fall from 1.817s to 1.387s. A separate diagnostic
reduces unique full-proof nodes from 143,397 to 113,982 and kernel samples from
645/626ms to 562/567ms. Kernel savings explain part, not all, of the complete-call
difference. The recurrence, zero pruning and cache keys are unchanged.

Tests should cover generic rings, rational coefficients, positive/composite
characteristic, subtraction, zeros and ordinary dense inputs. Check full proof
nodes, kernel time and complete declarations separately on the exact same input
and recurrence. Preserve all samples; do not infer performance from node counts
alone. This is the best first upstream PR because its semantic change is minimal.

## Reusable evaluator and target comparison

Mathlib already computes a normal expression and proof before wrapping them as a
`Simp.Result`. Its `normalizeBirdDet` and matrix-literal adapter are private in
the pinned `NormDet.lean`. Consider a small reusable API returning the computed
expression with its equality proof, while leaving the existing simproc and
`eval_det` surface intact.

A supplied-equality client can compare the target in the same scalar atom context
before cleaning intermediate output or traversing it again with a separate
`ring` call. Use reducible conversion only as a cheap shortcut. Unrestricted
conversion on concrete rings caused an experimental characteristic-two 4×4
process timeout; limiting transparency removed it. This is an implementation
hazard to test, not evidence that pinned Mathlib contains that shortcut bug.

Keep result production independent of a supplied answer. Do not prescribe Hex's
`Certified` type upstream: an existing expression/proof result is sufficient.
Measure result-producing and supplied-target paths separately, charging readable
output cleanup in the former. No controlled corpus-wide attribution currently
isolates the target-comparison API's share of the performance advantage.

## Scalar normalization policy

The experiment copies parts of `Ring.Common.eval` to vary treatment of division.
Replace that duplication with a narrow policy interface, if Mathlib maintainers
agree. Keep ordinary ring arithmetic, coefficient derivation and proof lemmas
shared. Preserve the existing behavior of `ring`, `ring_nf` and `norm_det` by
default; a customization interface should not silently change their normal forms.

A useful policy can distinguish constant denominators from symbolic ones, choose
whether to expand a quotient, and stop speculative normalization when an
intermediate result exceeds the permitted monomial count. Rejected speculation
must restore both Meta and atom state. Do not catch a heartbeat/resource exception
as an ordinary algebraic refusal. In a stronger comparison, re-normalize both
sides in a fresh atom context instead of retaining obsolete quotient atoms.

Evidence is specific: exposing monomial quotient factors improves a controlled
symbolic-row-denominator 5×5 comparison from 2.396s to 0.184s. Bounding discarded
numerator expansion improves the degree-eight quotient 4×4 comparison from
0.433s to 0.103s. Eager factor expansion also loses on independent quotients,
so neither observation justifies changing the global default to always expand.

## Selective quotient relations

Keep compact quotient atoms and index their multiplicative signatures. When
signatures indicate possible merging, construct actual scalar equality proofs
for selected products. Signatures never enter proof evidence. Distinguish a
factor from its inverse; a denominator may be zero. Use a sufficient private-
factor test to skip useless searches and invalidate it when atoms are added.

The measured relation method gives 0.306s versus Mathlib's 6.182s for a 5×5
identity-plus-rank-one example with product denominators. Independent quotient
6×6 comparisons have split pair directions and remain near parity. These are
whole-method comparisons, not an attribution to signature lookup alone. Some
small quotient losses have not been rerun with this method.

Before proposing a default upstream policy, cover shared denominators without
cancellation, powers, signs, zero denominators, target-only atoms and large sums.
Use persistent indices, scoped caches, per-side rewrite selections and explicit
budgets. Test atom-table rollback and cache reuse directly. General scalar
identities must drive selection, never determinant rank or matrix-family tests.
This is a later PR, separate from the compact congruence improvement.

## Combined recurrence equations and non-candidates

Combining the zero/successor unfolding equations slightly reduces proof structure.
A controlled ordinary comparison gives 1.208s versus 1.176s at 10×10; the small
margin does not establish a robust extra speedup. Ensure every new branch reaches
the shared cache insertion: an experimental early return bypassed it and caused
a large construction-time regression. A smaller shared proof is insufficient
if the evaluator repeatedly reconstructs it before sharing.

Do not upstream the experimental Boolean switches, matrix-shape dispatch,
blanket auxiliary-theorem opacity, or complete evaluator forks. Keep the Hex
numeric certificate/value algorithms separate. No Mathlib PR depends on adopting
Hex's SPECs or native libraries, and the Hex replacement need not wait for these
upstream proposals to be accepted.
