# HexHensel Lifting API Phase 6 Review

## Scope

Reviewed the public lifting surface in:

- `HexHensel/Basic.lean`
- `HexHensel/Linear.lean`
- `HexHensel/Quadratic.lean`
- `HexHensel/Multifactor.lean`
- `HexHensel/QuadraticMultifactor.lean`

The review checks the Phase 6 concerns from `PLAN/Phase6.md`: characterising
lemmas, downstream usability without unfolding executable algorithms, naming,
docstrings, and automation annotations.

## Summary

The production Hensel surface is broadly usable by downstream code. The key
bridge operations have coefficientwise characterisation lemmas and congruence
transport lemmas. The quadratic single-step API exposes factor, Bezout, combined
spec, monicness, and base-modulus preservation theorems. The quadratic
multifactor API is especially close to Phase 6 quality: it has the public
product-congruence spec, output size/boundary simp lemmas, per-output mod-`p`
preservation, per-output monicness, and constructors from the natural
`choosePrimeData`/mod-`p` boundary facts used by the Berlekamp-Zassenhaus bridge.

There are follow-ups before treating the whole executable Hensel API as polished.
They are mostly API-shape and convenience issues, not algorithmic correctness
issues.

## Findings

### Bridge Operations

`ZPoly.modP`, `FpPoly.liftToZ`, and `ZPoly.reduceModPow` have the expected
normal-form lemmas:

- `ZPoly.coeff_modP`
- `ZPoly.coeff_reduceModPow`
- `ZPoly.congr_reduceModPow`
- `ZPoly.reduceModPow_eq_of_congr`
- `ZPoly.reduceModPow_reduceModPow`
- `ZPoly.modP_reduceModPow`
- `FpPoly.coeff_liftToZ`
- `FpPoly.modP_liftToZ`

These are well-named for the local `ZPoly`/`FpPoly` API and have useful `@[simp]`
coverage where they normalise constructors or canonical reductions. The bridge
surface is suitable for downstream proofs without unfolding the executable
definitions in ordinary cases.

### Linear Lifting

The single-step contract `ZPoly.linearHenselStep_spec` matches the SPEC shape:
from product congruence modulo `p^k`, Bezout modulo `p`, and monicness of the
leading factor, it proves product congruence modulo `p^(k+1)`.

The iterative wrapper `ZPoly.henselLift_spec` is correct but still proof-engine
facing. It requires callers to provide:

- an initial `LinearLiftLoopInvariant`;
- a per-step `LinearLiftStepDegreeInvariant` for every loop state;
- a per-step Bezout preservation obligation for every loop state.

That is acceptable for the internal linear reference proof, but it is not a
polished Phase 6 consumer API. A downstream user cannot construct the linear
multifactor invariant from natural mod-`p` factorisation facts in the same way
they can for the quadratic production path.

### Quadratic Single-Step Lifting

`ZPoly.quadraticHenselStep` has the expected public theorem cluster:

- `quadraticHenselStep_factor_spec`
- `quadraticHenselStep_bezout_spec`
- `quadraticHenselStep_spec`
- `quadraticHenselStep_monic`
- `quadraticHenselStep_factor_congr_mod_base`

The statement shapes are good: callers reason through `ZPoly.congr` and
`DensePoly.Monic`, not by unfolding the correction algorithm. The split factor
and Bezout specs also make it possible to consume whichever half is needed
without destructuring the combined spec.

### Quadratic Iterated And Multifactor Lifting

The quadratic loop has a clean invariant package:

- `QuadraticLiftLoopInvariant`
- `QuadraticLiftLoopInvariant.of_product_bezout_monic`
- `QuadraticLiftLoopInvariant.prod_congr`
- `QuadraticLiftLoopInvariant.bezout_congr`
- `QuadraticLiftLoopInvariant.monic`
- `quadraticLiftLoopInvariant_step`

The public production wrapper `henselLiftQuadratic_spec` proves the target
product congruence modulo `p^k`, and companion lemmas cover base-modulus
preservation and monicness of both output factors.

The multifactor production API has the right list/array-shaped contract:

- `multifactorLiftQuadratic_spec`
- `quadraticMultifactorLiftInvariant_of_factorsModP`
- `QuadraticMultifactorLiftInvariant_of_choosePrimeData`
- `multifactorLiftQuadratic_size_eq_input`
- `multifactorLiftQuadratic_empty`
- `multifactorLiftQuadratic_singleton`
- `multifactorLiftQuadratic_each_congr_mod_base`
- `multifactorLiftQuadratic_each_monic`

These are sufficient for the current Berlekamp-Zassenhaus Mathlib bridge to
avoid unfolding the executable lifter. Existing downstream wrappers such as
`henselLiftData_liftedFactor_modP_eq_modPFactor`,
`henselLiftData_liftedFactor_injective_of_choosePrimeData`, and
`henselLiftData_liftedFactorProduct_univ_congr_core` consume this surface rather
than the implementation internals.

### Mathlib Boundary

Abstract uniqueness and coprimality transfer are correctly kept out of this
Mathlib-free library. `HexHenselMathlib/Correctness.lean` owns the
linear-vs-quadratic uniqueness statement, currently as
`multifactorLift_eq_multifactorLiftQuadratic`. That placement matches the SPEC.

## Recommended Follow-Up Issues

1. `HexHensel Phase 6: add linear multifactor invariant constructors from mod-p boundary facts`

   Target: `HexHensel/Multifactor.lean` and, if needed, `HexHensel/Linear.lean`.
   Add a constructor analogous to the quadratic
   `quadraticMultifactorLiftInvariant_of_factorsModP` /
   `QuadraticMultifactorLiftInvariant_of_choosePrimeData` path, or explicitly
   document that the linear lifter is proof-internal and not intended to have
   that consumer-level constructor.

2. `HexHensel Phase 6: expose iterated quadratic Bezout preservation at target precision`

   Target: `HexHensel/QuadraticMultifactor.lean`. The loop invariant carries
   Bezout congruence through every doubling step, and the single-step API exposes
   it, but the public `henselLiftQuadratic_spec` only returns product
   congruence. Add a companion theorem for
   `(lifted.s * lifted.g + lifted.t * lifted.h) ≡ 1 (mod p^k)` if downstream
   code needs the final witnesses directly.

3. `HexHensel Phase 6: audit simp/grind annotations for invariant projections`

   Target: the five reviewed files. The bridge normalisation lemmas have good
   `@[simp]` coverage, but invariant projection and constructor lemmas are mostly
   unannotated. Decide locally whether projections such as
   `QuadraticLiftLoopInvariant.prod_congr` and
   `LinearLiftLoopInvariant.product_congr` should remain explicit or receive
   automation attributes for recurring proof patterns.

## Conclusion

No source change is required for the current Berlekamp-Zassenhaus consumers. The
quadratic production path has the characterising lemmas and wrapper statements
expected for Phase 6 review. The remaining work is focused polishing: linear
reference-lifter constructor ergonomics, an optional final Bezout theorem for
the iterated quadratic wrapper, and a deliberate automation-annotation pass.
