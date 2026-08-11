# One canonical `Bounds 2`, and the bug the duplicates were hiding

## Accomplished

`Hex.ZMod64.boundsTwo` in `HexModArith/Residue.lean`, beside the class it
witnesses, is now the project's single `Bounds 2`. The five public copies
are gone: `HexBerlekamp/Irreducibility.lean`, `HexConway/Table.lean`,
`HexGF2Mathlib/Basic.lean`, `HexGF2Mathlib/Field.lean` twice, and
`HexGFqMathlib/GF2q.lean`. No consumer needed migrating, since anything
using `ZMod64` already imports the module that defines it.

That is a smaller change than the opt-in-scope scheme sketched previously,
and it is enough: `Bounds p` is a `Prop`, so several witnesses were never a
coherence risk, only ambiguity and unreadable diagnostics. One reachable
candidate settles both.

Removing the duplicates then exposed a real bug they had been masking.
`HexPolyFp/SquareFree.lean` declared `private instance
squareFreeGuardBoundsTwo`. **`private` hides the name but leaves the
instance in the table for importing modules**, so with the public copies
gone, instance search in `HexBerlekampZassenhausMathlib/FactorPolyTests.lean`
selected it and emitted a term naming
`_private.HexPolyFp.SquareFree.0.Hex.FpPoly.squareFreeGuardBoundsTwo`, which
cannot legally be referenced there. This is the same failure shape as the
original leak, from a different source, and it was one instance-ordering
change away from firing on its own. Both guards are now `local instance`.

`local` is therefore the right marker for an instance you do not want
exported, and `private` is actively wrong: it keeps the hazard and only
hides the name. Written up in the `hex-lean-mathlib-boundary` skill, since
this has now caused two separate failures.

Two manual chapters, `HexBerlekamp` and `FactorTactics`, turned out to have
no `Bounds 5` witness of their own: their displayed examples compiled only
because the `SquareFree` guard was leaking into them. Both now declare
`local instance boundsFive`. The three chapters that already had one showed
`private instance`, the form the skill now says never to use, so they are
converted too; a manual should display the idiom it recommends.

Verified against `ci.yml`'s `HEX_LIB_TARGETS` plus `HexGF2Mathlib`,
`HexGFqMathlib` and `hexstrassen_compare` (9673 jobs), and separately
against `HexManual` (9717 jobs), which `ci.yml` builds as its own step and
which an earlier round of this change missed.

## Current frontier

`refactor/canonical-bounds-two`.

## Next step

`Bounds` witnesses at other moduli are all single-declaration or scoped, so
none of them is ambiguous. The remaining `private instance` occurrences live
in conformance, bench, manual chapters and `reports/scratch`, none of which
any module imports, so they cannot leak; converting them to `local` would be
tidiness rather than a fix.

## Blockers

None.
