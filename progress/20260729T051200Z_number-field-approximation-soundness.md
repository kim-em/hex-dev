# Number-field approximation soundness

## Accomplished

- Proved the semantic coefficient, zero, and natural-degree correspondence for
  `AlgebraicPoly.toPolynomial`.
- Proved successful-refinement precision and the closed-disc semantics of
  dyadic complex-ball addition, multiplication, inversion, rational rounding,
  and Horner evaluation.
- Proved `QAdjoin.approx_sound` for both successful refinement and fallback.
- Made the positive-precision exact-dyadic test proof-usable across the module
  boundary and added exact-versus-rounded regression guards.
- Incorporated independent review feedback by reusing Lean's core dyadic
  rounding bounds, making the Horner initializer explicit, and preserving the
  public `Array.foldr` definition of algebraic-polynomial interpretation.
- Verified the complete repository, NumberField and tower conformance targets,
  fixture emitter, and all eight NumberField benchmarks.

## Current frontier

The cohesive NumberField semantic-foundations milestone is ready to publish as
one pull request. Its proof changes introduce no new `sorry` or `axiom`.

## Next step

Publish the single milestone pull request, monitor its individual GitHub
Actions jobs, and merge it before beginning any further NumberField or tower
work.

## Blockers

None for this milestone. `RefinedIsolation.refineTo?_isSome` and
`QAdjoin.approx_radius` remain as pre-existing follow-up obligations and should
be handled together with the refinement-completeness infrastructure they need.
