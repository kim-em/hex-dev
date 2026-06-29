# 20260604T023008Z Codex SPEC clause review

## Accomplished

Reviewed the proposed `SPEC/Libraries/hex-matrix.md` clause forbidding
bridge-layer proofs from citing sorry-bearing Mathlib-free theorems.

Checked the surrounding matrix and Gram-Schmidt proof-surface text, plus
project-wide doctrine in `SPEC/design-principles.md`, `SPEC/testing.md`,
and `PLAN/Conventions.md` to assess precision, placement, and
anti-loophole coverage.

## Current frontier

The proposed clause identifies the right failure mode from PR #6502, but
its normative scope is too local and its wording does not explicitly cover
transitive dependencies, wrappers, copied proof debt, or cases where a
bridge theorem legitimately needs an executable Mathlib-free statement as
data/specification rather than as proof authority.

## Next step

Move the general rule to project-wide proof-layer hygiene text or
`SPEC/design-principles.md`, then have per-library proof-surface sections
cross-reference it and keep only local examples.

## Blockers

No blocker. This was a review-only turn; no Lean code or SPEC source was
modified.
