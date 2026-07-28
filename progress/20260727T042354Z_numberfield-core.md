# HexNumberField core representations

## Accomplished

- Activated `HexNumberField`, registered its Lake target, added its umbrella,
  and moved the immutable SPEC into the active library layout.
- Implemented runtime checked-irreducibility evidence, fixed-field rational
  coordinates, factorization-lazy roots, canonical algebraic numbers behind a
  private constructor, multiplicity-bearing roots, and total root sets.
- Added the checked canonical-construction boundary: it re-runs the fixed
  bounded isolator and selects the canonical matching disc before constructing
  an `AlgebraicNumber`.
- Implemented exact closed-disc zero membership, canonical and lazy zero
  predicates, and polynomial-plus-root canonical equality.
- Built the new library and passed DAG, copyright, line-count, forbidden-form,
  and whitespace checks with no new sorries.

## Current frontier

The core data invariants are represented without exposing a raw canonical
constructor. `HexNumberField` remains at Phase 1 because the remaining
fixed-field, conversion, lazy arithmetic, disambiguation, semantic-polynomial,
and roots modules are not yet implemented. Its recorded Phase 1 completion is
also dependency-blocked by `HexBerlekampZassenhaus.done_through = 0`.

## Next step

Publish this core milestone, then implement reduced `QAdjoin` arithmetic and
threaded approximation in `QAdjoin.lean` while the earlier PR reviews continue.

## Blockers

No implementation blocker. The dependency-phase gate prevents advancing
`HexNumberField.done_through` until HexBerlekampZassenhaus reaches Phase 1.
