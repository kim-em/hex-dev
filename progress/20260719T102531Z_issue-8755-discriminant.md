# Accomplished

- Moved the generic discriminant root-product development to
  `HexPolyZMathlib/Discriminant.lean` and the sharp column-Hadamard inequality
  to `HexPolyZMathlib/Hadamard.lean`, preserving every declaration and proof.
- Kept thin public-import compatibility modules at the old
  `HexRealRootsMathlib` paths and changed `Separation.lean` to consume the
  shared modules directly.
- Updated both umbrella descriptions and both affected SPEC/module maps.
- Received a Claude Opus review with no substantive concerns; clarified the
  real-roots umbrella wording in response to its sole optional documentation
  observation.
- Passed focused builds, both moved-module Mathlib linters, DAG/copyright/
  line-count/phase checks, diff checks, and the full 9,378-job `lake build`.
  The two `simpNF` findings in `HexRealRootsMathlib.Separation` reproduce
  unchanged on merged `main` and are not introduced by this extraction.
- Confirmed geometry PR #8774 passed CI and merged, and opened #8775 for the
  following generic Mahler/Vandermonde extraction.

# Current frontier

Issue #8773 is implementation-complete and ready to commit, rebase onto the
geometry merge, and publish as the next PR in the #8755 merge train.

# Next step

Commit this extraction, rebase it on current `origin/main`, rerun the affected
build checks, push and open the reviewed PR, enable auto-merge after checking
conflicts, then begin #8775 while CI runs.

# Blockers

Plan item 2 / #8772 remains paused because the requested squarefree-over-ℤ
equivalence is false for nonprimitive polynomials; the concrete `4X + 4`
counterexample and corrected rational-cast target are posted on #8772 and
#8755. This does not block the generic analysis extraction chain.
