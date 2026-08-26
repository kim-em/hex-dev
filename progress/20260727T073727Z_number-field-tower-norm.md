# Number-field tower one-level norms

## Accomplished

- Added a runtime-indexed lower-tower coefficient carrier with recursive field
  operations for generic polynomial gcd and resultant algorithms.
- Implemented direct one-level Trager elimination
  `Res_Y(m(Y), g(X - cY))` over the immediately lower tower.
- Added derivative, monic normalization, and executable squarefreeness checks
  for runtime-indexed tower polynomials.
- Implemented the exact `choose(d*m, 2) + 1` shift budget, the deterministic
  signed shift enumeration, and first-squarefree-norm search.
- Added compiled norms over `Q(sqrt(2))` and over
  `Q(sqrt(2), sqrt(3))`, including repeated-norm detection.
- Verified `lake build HexNumberFieldTower.Norm` and the full `lake build`.

## Current frontier

The finite Trager shift step now produces squarefree norms over the lower tower.
Recursive factorization and gcd recovery of lifted lower factors remain to be
connected.

## Next step

Add checked factorization result types and reconstruction, implement Yun
decomposition on runtime tower polynomials, then recurse through Trager norms
and recover factors by shifted gcd.

## Blockers

None.
