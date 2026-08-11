# Reading a coefficient literal off on the Mathlib side

## Accomplished

`factor_poly` on a `Polynomial ℤ` returns factors as
`factors.map HexPolyZMathlib.toPolynomial` over `Hex.DensePoly.ofCoeffs`
literals, so nothing could state what factorization it actually found:
`cyclo.factors = [Φ₅, Φ₇]` was not `rfl`, and `simp` stalled at
`toPolynomial (ofCoeffs #[1, 1, 1, 1, 1])` because no lemma normalized it.

- `HexPolyMathlib.toPolynomial_ofCoeffs` closes that gap:
  `toPolynomial (ofCoeffs cs) = ∑ i ∈ range cs.size, C (cs.getD i 0) * X ^ i`.
  Stated with `C _ * X ^ i` rather than `monomial i _` so a use site needs
  no `C_mul_X_pow_eq_monomial` rewrite of its own.
- Tagged `@[simp, grind =]`. A full `lake build` (9754 jobs) says the only
  downstream effect is that one case of
  `HexNumberFieldTowerMathlib.NormCore.Basic` now closes by `simp` alone;
  its four-line tail and two now-unused simp arguments are gone.

Concretely this turns the announcement's factoring example into a
statement of the answer rather than a statement about the product:

    example : cyclo.factors = [1+X+X^2+X^3+X^4, 1+X+X^2+X^3+X^4+X^5+X^6] := by
      simp [cyclo, Hex.FactoredPoly.ofZ, Finset.sum_range_succ]

## Current frontier

`feat/to-polynomial-of-coeffs`, branched from main, independent of the
release-tooling work on `docs/release-token-scope`.

## Next step

Nothing pending on this thread.

## Blockers

`Hex.FactoredPoly.ofZ` cannot be dropped from that simp set, so the call
cannot get below three arguments. Projection lemmas (`factors_ofZ`,
`scalar_ofZ`) look like the fix and do not work: an emitted term fills its
certificate slots with `Eq.refl true`, which is only type-correct once
`beqCoeffs` computes on the literals, so at the reducible transparency
`rw`/`simp` match under, the `ofZ` application is ill-typed and no pattern
can match it. Unfolding `ofZ` avoids matching altogether, which is why only
that works. Two such lemmas were written, confirmed dead, and removed.
