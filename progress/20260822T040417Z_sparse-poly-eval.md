# hex-sparse-poly: evaluation, derivative, substitution (milestone 4)

## Accomplished

- `HexSparsePoly/Eval.lean`: gap-Horner `eval` (identity-free binary
  powering `pow1`/`mulPow` over the exponent gaps), with
  `eval_toDense` proved at `Lean.Grind.Semiring` exactly as the SPEC
  demands (no coefficient is commuted past a power of `x`).
- `derivative` as a filtered coefficient map dropping the `e = 0` term
  and any vanishing `(e : R) * c`, with `coeff_derivative`,
  `derivative_toDense`, `derivative_add` (all proved) and
  `derivative_mul` by transport through the dense product rule.
- `substPow` (`O(t)` exponent scaling for `k ≥ 1`; the `k = 0` case
  canonicalises through `ofTerms`), with `coeff_substPow_mul` and
  `coeff_substPow_of_ne` proved.
- `substScale` computing the powers of `a` from the exponent gaps
  (`substScaleGo` walk, canonicality proved), and `compose` as the
  gap-powered fold of scaled powers of `t` (`polyPow1`).

## Current frontier

Six `sorry`s remain, all in Eval's §Agreements: the `compose`
characterisation pack (`substPow_eq_compose`, `eval_substPow`,
`eval_compose`, `compose_toDense`, `substPow_toDense`) and
`coeff_substScale`. They need a coefficient/fold characterisation of
`compose`'s stateful gap-powering walk; scheduled for the Phase-5
implementation work loop.

## Next step

Milestone 5a (`HexSparsePoly/Euclid.lean`): `divModMonic`, `divMod`,
`gcd`, `divExactMonic?`, `divMonomial?` through the conversions, with
the transported law packages; then bump `done_through: 1`.

## Blockers

None.
