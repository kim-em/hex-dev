# Progress — BHKS CLD claim audit

## Accomplished

Reviewed the latest progress note, the BHKS fast-path SPEC, and the primary
BHKS paper text around the CLD lattice, Lemma 3.2, Theorem 4.3, Proposition 4.4,
and Theorem 4.6. Evaluated the attached claim without changing Lean sources.

Main conclusion: the affine separability objection to transporting a Sylvester
determinant through a non-affine coefficient cut is mathematically correct, but
the stronger rollback conclusion is too pessimistic. The published proof uses a
resultant contradiction on the unscaled `H := Φ(g) mod v^ell`, with smallness
derived from the lattice/rounding bounds, not a resultant of the high-bit cut
polynomial itself.

## Current frontier

The proof strategy should distinguish the executable cut/high-bit lattice vector
from the uncut CLD polynomial used in the resultant. A Lean proof can likely be
salvaged by reconstructing and bounding the uncut corrected `H` from the cut
coordinates and low-residue estimates.

## Next step

Re-author any pending BHKS Group-D directive so its valuation endpoint is
`Res(f, H)` for the uncut corrected CLD polynomial, while the cut lattice only
supplies coefficient/norm bounds for `H`.

## Blockers

No code blocker found in this turn. The blocked premise is the false attempt to
apply `p^(k*d) ∣ Res(f, auxCut)` directly to the high-bit quotient polynomial.
