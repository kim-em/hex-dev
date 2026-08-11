# Naming the last anonymous Bounds instances

## Accomplished

Follow-up to the instance leak fixed on `fix/bounds-instance-leak`. Two
library modules still declared anonymous `ZMod64.Bounds` instances, so they
carried auto-generated `instBoundsOfNatNat_*` names, which is what made the
original failure so hard to read.

- `HexBerlekamp/Irreducibility.lean`: one, now `boundsTwo`.
- `HexConway/Table.lean`: six, now `boundsTwo` ... `boundsThirteen`.

Visibility is deliberately unchanged. Scoping them `local`, as was done for
the test fixtures, was tried first and is wrong here: it breaks
`HexConway/Certificates.lean` (101 errors) and
`HexBerlekampMathlib/Irreducibility.lean` (2). Those instances are
load-bearing for downstream modules, so the fix is naming only.

Verified against the `HEX_LIB_TARGETS` set from `ci.yml`, 9643 jobs, green.
The default `lake build` target set omits the test libraries, which is how
an earlier version of the sibling fix reached CI broken.

## Current frontier

`refactor/name-bounds-instances`.

## Next step

Two things this deliberately does not do.

Anonymous `ZMod64.Bounds` instances remain elsewhere:
`HexGFqMathlib/GF2q.lean`, `HexGF2Mathlib/Basic.lean`, two in
`HexGF2Mathlib/Field.lean`, and `HexBerlekampZassenhaus/Classical/Obstruction.lean`
(the last over a named constant rather than a numeral), plus several bench
modules. Naming those is the same mechanical change.

More substantially, naming is diagnosability, not hazard removal. Public
instances for specific numerals are still visible to every importing
module's instance search, and there are now visibly two equal-priority
candidates for `Bounds 2` inside `HexConway/Table.lean`: its own
`Hex.Conway.boundsTwo`, and `Hex.Berlekamp.boundsTwo` reaching it through
`HexBerlekamp.RabinSoundness`, which publicly imports
`HexBerlekamp.Irreducibility`. The structural fix is one canonical witness
per numeral in a low-level `ZMod64` module, registered locally or through an
opt-in scope at each consumer; that means migrating the consumers, which is
why it is not folded in here.

## Blockers

None.
