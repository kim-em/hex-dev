# Accomplished

- Added `Arithmetic.Coeff`, a fixed-width lower-tower coefficient carrier for
  recursive polynomial xgcd during tower inversion.
- Routed `invCoords` through canonical coefficients instead of the
  noncanonical `RawElem` wrapper, preserving the existing executable results.
- Proved `invCoords_size`, including every defensive fallback branch.
- Rebuilt the tower library, Mathlib companion, manual, conformance target,
  and benchmark target; all 19 benchmark fixtures retain their expected hashes.

# Current frontier

`map_inv` remains the sole primitive arithmetic correspondence gap. Its next
proof layer is a lawful field structure on `Arithmetic.Coeff lower`, transferred
through injective complex denotation, together with generic dense-polynomial
division and gcd laws over a field.

# Next step

Add the reusable field-level `DensePoly.DivModLaws` and `DensePoly.GcdLaws`
bridge, then use it in the recursive `invCoords` denotation proof and close
`NumberTower.map_inv`.

# Blockers

None. Second-opinion review is being deferred asynchronously while the stacked
implementation proceeds.
