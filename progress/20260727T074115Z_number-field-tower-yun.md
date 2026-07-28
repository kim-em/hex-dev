# Number-field tower Yun decomposition

## Accomplished

- Added runtime and public fixed-tower Yun decomposition with explicit positive
  multiplicity indices.
- Added exact Yun reconstruction checks requiring monic squarefree components
  and equality with the monic input.
- Added a rational base case that clears to a primitive integer associate,
  calls Berlekamp–Zassenhaus, expands multiplicities, normalizes factors monic,
  and accepts only exact rational reconstruction.
- Added compiled repeated-factor regressions over `Q` and `Q(sqrt(2))`, plus a
  reducible rational base-factorization regression.
- Verified `lake build HexNumberFieldTower.Factor` and the full `lake build`.

## Current frontier

Yun separation and the rational recursion base are complete. A squarefree
component over a proper tower can now be shifted and normed, but recursive
lower-factor recovery is not yet connected.

## Next step

Implement recursive Trager factorization: factor the selected squarefree norm
over the lower tail, lift each lower factor, recover shifted gcd factors, undo
the shift, and verify reconstruction.

## Blockers

None.
