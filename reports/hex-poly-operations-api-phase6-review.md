# HexPoly Operations API Phase 6 Review

## Scope

Reviewed the public executable-operation surface in `HexPoly/Operations.lean`
against `SPEC/Libraries/hex-poly.md` and `PLAN/Phase6.md`.

This review covered:

- scalar multiplication and shifts;
- coefficient laws for addition, subtraction, negation, multiplication, and
  derivative;
- zero and constant wrappers for evaluation and composition;
- downstream use in `HexPoly/Euclid.lean`, `HexPolyFp/Compose.lean`,
  `HexHensel`, `HexGFqRing`, and `HexBerlekampMathlib`.

This is a review-only Phase 6 slice. It does not edit Lean source.

## Summary

The core arithmetic surface is mostly in good shape. `Operations.lean` exposes
named coefficient laws for the executable definitions instead of forcing
callers to unfold loops:

- `coeff_scale`, `coeff_scale_semiring`, `coeff_shift`, and
  `coeff_shift_scale_semiring` characterize scalar multiplication and shifts.
- `coeff_add`, `coeff_add_semiring`, `coeff_sub`, `coeff_sub_ring`,
  `coeff_neg`, and `coeff_neg_ring` cover the additive wrappers.
- `coeff_mul` exposes the schoolbook multiplication loop through
  `mulCoeffSum`; `HexPoly/Euclid.lean` then reifies that fold into diagonal
  sums and proves the expected algebraic laws such as `mul_comm_poly`,
  `mul_assoc_poly`, `mul_add_right_poly`, and `monomial_one_mul_poly_eq_shift`.
- `eval_zero`, `eval_C_semiring`, and `eval_monomial_semiring` provide the
  useful scalar-evaluation base cases.
- `coeff_derivative`, `coeff_derivative_semiring`,
  `derivative_C_semiring`, `derivative_monomial_zero_semiring`, and
  `derivative_monomial_succ_semiring` expose the formal derivative behavior;
  `HexPoly/Euclid.lean` builds the product rule on top of this surface.

Public declarations and non-obvious private helpers have docstrings, and the
module remains Mathlib-free.

I found two concrete Phase 6 polish gaps. Neither is a correctness issue.

## Follow-Up Recommendations

### 1. Promote a core composition characterization

Filed as #5970: `HexPoly Phase 6: promote core compose power-sum API`.

`DensePoly.compose` currently has only zero/constant wrappers in
`HexPoly/Operations.lean`. That is enough for tiny normalization goals, but it
does not give downstream callers a general way to reason about substitution.
`HexPolyFp/Compose.lean` consequently rebuilds a local compose-as-power-sum
surface (`composeCoeffPowerSumUpTo`,
`compose_eq_coeff_power_sum_upTo_bound`) before proving `compose_sub` and the
Berlekamp substitution lemmas.

Recommended implementation shape:

- add a reusable core power-sum or coefficient-indexed characterization for
  `DensePoly.compose`;
- expose semiring/ring-specialized wrappers for common substitution laws where
  the hypotheses are manageable;
- migrate `HexPolyFp/Compose.lean` to use the core surface and delete local
  duplicate infrastructure where possible.

### 2. Tune `grind` annotations for operation laws

Filed as #5971: `HexPoly Phase 6: tune automation annotations for operation
laws`.

The operation API has good `[simp]` coverage for semiring/ring-specialized
normalization lemmas, but `HexPoly/Operations.lean` currently has no
`@[grind]` annotations on the operation theorem surface. Phase 6 explicitly
calls out `grind` support as part of the automation bar, and downstream proofs
already use repeated manual rewrites through coefficient laws before handing
the resulting scalar goals to `grind`.

Recommended implementation shape:

- audit coefficient laws such as `coeff_scale_semiring`, `coeff_shift`,
  `coeff_shift_scale_semiring`, `coeff_add_semiring`, `coeff_sub_ring`,
  `coeff_neg_ring`, `coeff_derivative_semiring`, and `coeff_zero`;
- try conservative `@[grind =]` or `@[simp, grind =]` annotations on equations
  that should be used as directed rewrites;
- leave any theorem unannotated if it loops or bloats search, and document the
  local reason in the PR.

## No Follow-Up Needed

No follow-up is needed for the basic coefficient characterizations of scale,
shift, addition, subtraction, negation, multiplication, scalar evaluation base
cases, or derivative. These already meet the Phase 6 encapsulation criterion:
callers can reason through named lemmas and algebraic wrappers instead of
unfolding executable array/list implementations.

No follow-up is needed for import or namespace cleanup in this slice. The file
imports only `HexPoly.Dense` and `Init.Data.Array.Lemmas`, stays under
`Hex.DensePoly`, and keeps implementation-only fold/list helpers private.

## Verification

Checked for overlapping open follow-up work with:

- `coordination list-unclaimed`
- `gh issue list --state open --label agent-plan --search "HexPoly Phase 6"`
- `gh issue list --state open --search "compose_sub OR compose_add OR compose_mul HexPoly"`

The only open overlap before filing follow-ups was this review issue.
