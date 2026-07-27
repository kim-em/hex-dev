# RCF executable Sturm-replay milestone

## Accomplished

- Added the `Hex.RCF.SturmStep` and `SturmReplay` certificate records and a
  multiplication-only Boolean checker for head, nonzero, degree, terminal,
  derivative, step-count, scale, quotient, and recurrence invariants.
- Proved checker success constructs `HexRealRootsMathlib.ZReplay` and implies
  real Sturm-chain validity, squarefreeness, exact interval counts, and the
  exact total real-root count.
- Added a compiled builder that instruments the existing pseudo-remainder loop
  with the invariant `scale A prev = Q * cur + r`, retains the literal input as
  chain head, rejects exhausted/nonsquarefree traces, and returns only
  checker-approved candidates.
- Added valid and malformed checker regressions, zero-step and multi-step
  builder paths, a negative-leading divisor, a nonprimitive input, endpoint-
  sensitive literal counts, and rejected constant/zero/repeated-root inputs.
- Updated the RCF SPEC with the exact builder invariant and file organization,
  and activated the modules through the `HexRCF` umbrella.
- Incorporated a Sol builder-invariant audit and two fresh Claude Opus reviews.
  The first found no soundness defect but required broader branch coverage; the
  follow-up verified those gaps closed and returned a merge-ready verdict.
- Passed `lake build HexRCF HexRealRootsMathlib` (8,787 jobs) and the copyright,
  line-count, DAG, phase-4, Mathlib-free bench, conformance-target, diff, and
  forbidden-proof-token checks.

## Current frontier

Issue #8899 is ready to publish. The RCF trust boundary can now consume a
literal polynomial and replay certificate without evaluating pseudo-division,
gcd, primitive-part normalization, square-free-core computation, or root
search in the checker.

## Next step

Define the top-level certificate carrier package and generalized literal
isolation records. Recompute atom polynomials and their product from the
sentence, check the two carrier factor/derivative identities, connect carrier
roots to the atom-root union, and use the accepted `SturmReplay.count` and
`total` values for isolation soundness.

## Blockers

None.
