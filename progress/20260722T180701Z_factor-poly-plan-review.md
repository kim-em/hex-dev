# `factor_poly` / `irreducibility` implementation-plan review

## Accomplished

- Audited the proposed plan against the current free and Mathlib bridge declarations.
- Verified the principal Rabin, mod-p transfer, factorization soundness, transport,
  and decidability theorem shapes.
- Identified feasibility gaps in opaque closed-term certification, free-layer ZPoly
  completeness, provider fallback/goal-mode design, plain-import reduction, and the
  Mathlib-free Eisenstein translation proof.
- Checked the stated examples: `X^4 + 1` is Eisenstein after translating by `1` at
  prime `2`; `X^4 - 10X^2 + 1` is not shift-Eisenstein for any integer shift.

## Current frontier

Review complete. No implementation files were changed.

## Next step

Revise the plan around a short feasibility phase: prototype provider discovery and
goal-mode execution under plain imports, define the exact closed-term trust boundary,
and decide whether free `ZPoly.factor_poly` is explicitly partial or gains a complete
free certificate route.

## Blockers

- The existing free certificate menu cannot prove irreducibility of every factor
  returned by `ZPoly.factorize`; unconditional per-factor soundness currently lives in
  `HexBerlekampZassenhausMathlib`.
- Imported opaque closed definitions cannot be equated to elaborator-evaluated literals
  merely from `evalExpr`; a kernel-checkable bridge or a stricter input contract is
  required.
