# Review noncomputable `@[csimp]` specs

## Accomplished

- Reviewed the current `noncomputable` markings for the eight active
  proof-backed `@[csimp]` specification definitions:
  `Hex.Nat.choose`, `Vector.dotProduct`, `Matrix.mul`, `ZMod64.add`,
  `ZMod64.sub`, `DensePoly.trimTrailingZeros`, `DensePoly.mul`, and
  `DensePoly.divModArrayAux`.
- Grepped the repository for live `@[csimp]` declarations and found no
  additional active source-level spec/implementation pair that needs the same
  marking for consistency.
- Probed representative compiled-call shapes against the current tree:
  direct application, partial application, first-class function binding,
  higher-order argument passing, and a `Decidable`/`decide` use of
  `Hex.Nat.choose`. These compiled/evaluated successfully.
- Reviewed design principle 11 wording for the main mechanism and identified
  one wording nuance: `csimp` redirects compiled occurrences that survive to
  code generation; theorem/proof/kernel normalization still sees the public
  specification.

## Current frontier

- No source change recommended from this review. The only optional polish would
  be wording principle 11 a little less absolutely around "every compiled
  caller".

## Next step

- Use the second-opinion findings in the PR review or issue comment.

## Blockers

- None.
