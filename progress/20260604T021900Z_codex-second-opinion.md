# 20260604T021900Z Codex second-opinion review

## Accomplished

Reviewed the residual `getArrayEntry_scaledCoeffRowsSchur_eq` sorry and its
surrounding architecture in `HexGramSchmidt/Int.lean`, including
`BareissGramRowInvariant`, the quotient provider, the PSD column-zero lemma,
the Schur/Bareiss correction helpers, and the current downstream bridge use in
`HexGramSchmidtMathlib/Int.lean`.

Checked the project doctrine in `.claude/CLAUDE.md`, the post-#6505
Mathlib-bridge clause in `SPEC/Libraries/hex-gram-schmidt.md`, and the recent
conversation transcript sections around #6510. Also searched the Cramer,
scaled-coefficient, adjugate, and cofactor-row-pairing infrastructure in
`HexGramSchmidtMathlib` and `HexMatrix`.

Attempted to use the local second-opinion skill's Claude wrapper for an
independent review, but it failed before returning substantive output with
`API Error: Unable to connect to API (FailedToOpenSocket)`.

## Current frontier

The current provider type still quantifies over arbitrary
`BareissGramRowInvariant` witnesses, which is too strong. Existing bridge facts
identify matrix entries, determinants, bordered minors, or rational
Gram-Schmidt coefficients, but not the integer coefficient vector carried by
the row invariant.

The adjugate/cofactor infrastructure is useful raw material for a canonical
coefficient construction, but it does not already expose the missing canonical
row-invariant coefficient characterization.

## Next step

Prefer a route-A-style design: introduce a separately defined canonical
coefficient vector with determinant/cofactor characterization, then refactor
the provider surface so it only applies to canonical loop states and can be
constructed without circularly depending on
`bareissGramRowInvariant_noPivotLoop_initial`.

Before implementation, split the public theorem/API dependency graph so
Mathlib-side scaled-coefficient facts no longer prove themselves through the
Mathlib-free residual theorem they are meant to close.

## Blockers

No code blocker for this review-only turn. The external Claude second-opinion
tool was unavailable due to socket/API connectivity, so the verdict is based on
local code inspection rather than a second model's substantive output.
