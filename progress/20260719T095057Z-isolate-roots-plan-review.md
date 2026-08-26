# `isolate_roots` implementation-plan review

## Accomplished

- Reviewed the proposed term elaborator against the current real-root certificate,
  Mathlib companion, dense-polynomial, decomposition, and certificate-reification
  implementations.
- Confirmed that root-predicate transport is sound and that `aeval` supports the
  intended `Int`/`Rat`/`Real` coefficient rings with their canonical algebra maps.
- Traced the downstream kernel-reduction obligations and identified missing closure
  around private Sturm helpers, decidable-instance bodies, dense-polynomial equality,
  and the Core nonempty-array equality bug.
- Checked pinned Mathlib's polynomial radical, gcd/derivative, and root-multiplicity
  APIs. There is no direct `p / gcd(p,p') = radical p` shortcut; a focused
  root-multiplicity proof is the most promising bridge.
- Identified additional design risks in constant-polynomial handling, coefficient
  reflection, exact width elaboration, dependent evaluation, refinement/replay
  recomputation, structure ergonomics, and verification scope.

## Current frontier

- The plan is architecturally viable but should be revised before implementation.
- The largest proof item remains the executable square-free-core/root-set bridge;
  the exposure pass and the polynomial-expression interpreter are also larger than
  currently estimated.
- No library source files were changed.

## Next step

- Revise the PR decomposition around a minimal replay constructor/call graph, a
  proof-producing polynomial reifier, a special or uniform square-free-core path
  that handles nonzero constants, and a generic Mathlib lemma for roots of
  `p / gcd p p.derivative`.
- Prototype cached-chain refinement and replay before committing to the literal
  per-field `by decide` certificate shape.

## Blockers

- None for the review. The Core `Array.instDecidableEqImpl` module-system bug must
  either be avoided in emitted proofs or fixed upstream before relying on structural
  `DensePoly` equality decisions downstream.
