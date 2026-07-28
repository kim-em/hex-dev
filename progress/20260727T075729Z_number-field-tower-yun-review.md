# Accomplished

- Replaced the repeated-gcd loop with Yun's characteristic-zero derivative-correction recurrence.
- Strengthened `checkYun` with zero handling, strictly increasing multiplicities, and pairwise-coprime components.
- Made the fixed-tower Yun entry point checked, gave the rational base factorizer a typed squarefree input boundary, and rejected unexpected Berlekamp–Zassenhaus multiplicities.
- Added regressions for zero, split multiplicities, the checked public boundary, and nonsquarefree rational input.
- Rebuilt `HexNumberFieldTower.Factor` successfully.

# Current frontier

Yun decomposition now matches the specified algorithm and its local checker validates the canonical decomposition shape. The full Trager driver still needs to require this Yun certificate and reject duplicate adjacent irreducible factors.

# Next step

Propagate this correction through the Yun and Trager PRs, tighten the full factorization checker, then address the validated tower representation before adjoining roots.

# Blockers

None.
