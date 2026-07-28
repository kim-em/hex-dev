# Number-field tower Trager factorization

## Accomplished

- Implemented generator shifts, lower-polynomial embedding, shifted gcd
  recovery, and inverse shifting for one Trager recursion level.
- Added structurally recursive squarefree factorization through lower tower
  tails, with exact reconstruction before returning recovered factors.
- Added the full Yun-plus-Trager driver with scalar extraction, explicit
  multiplicities, canonical lexicographic sorting, and recursive executable
  irreducibility replay.
- Added the public `checkFactorization`, dependent `Factorization`, and
  `factor?` APIs from the tower SPEC.
- Added compiled regressions for a collision search that first succeeds at
  shift 2, an irreducible component, repeated factors, zero/constants, and the
  public dependent result over `Q(sqrt(2))`.
- Verified `lake build HexNumberFieldTower.Factor` and the full `lake build`.

## Current frontier

Complete factorization is executable and self-checking. The checker is not yet
stored as an invariant of each constructed level, so the representation must
be refactored before the Mathlib field-law proofs rely on tower validity.

## Next step

Tie level construction definitionally to the relative irreducibility checker,
then implement fixed-embedding factor selection for `adjoin?`.

## Blockers

None.
