# Naming the last anonymous Bounds instances

## Accomplished

Completes the audit begun on `refactor/name-bounds-instances`. Eight
anonymous `ZMod64.Bounds` instances are now named:

- `HexGF2Mathlib/Basic.lean`, and two in `HexGF2Mathlib/Field.lean`
  (`GF2n` and `GF2nPoly`, so both can be `boundsTwo`);
- `HexGFqMathlib/GF2q.lean`;
- `HexBerlekampZassenhaus/Classical/Obstruction.lean`, over the named
  constant `obstructionPrime` rather than a numeral;
- three in `bench/HexStrassen/Compare.lean`.

Visibility is unchanged throughout, as on the previous pass.

Three anonymous instances are deliberately left, in
`HexManual/Chapters/{HexGFqField,HexGFqRing,HexPolyFp}.lean`. They sit
inside ```lean blocks that the published manual renders, so naming them
would add noise to a worked example for no reader benefit, and they are
`private`, so they cannot be captured from another module.

Verified against `ci.yml`'s `HEX_LIB_TARGETS`, plus `HexGF2Mathlib`,
`HexGFqMathlib` and `hexstrassen_compare`, which the CI list does not
cover: 9673 jobs, green.

## Current frontier

`refactor/name-remaining-bounds`.

## Next step

The duplication this makes legible is now the whole of what is left.
Public `Bounds 2` witnesses exist in `HexBerlekamp.Irreducibility`,
`HexConway.Table`, `HexGF2Mathlib.Basic`, `HexGF2Mathlib.Field` twice, and
`HexGFqMathlib.GF2q`. Any module importing more than one sees several
equal-priority candidates. The fix is one canonical witness per modulus in a
low-level `ZMod64` module, registered locally or by an opt-in scope at each
consumer, which means migrating every consumer and so wants to be its own
piece of work.

## Blockers

None.
