# GF2 module expose diagnosis

## Accomplished

Reviewed the local `HexGF2.Basic` definitions involved in the module-system
migration question. Confirmed that exposed computational definitions such as
`normalizeWords` and `highestSetBit?` unfold through private helpers including
`trimTrailingZeroWordsList`, `highestSetBitBelow?`, and `wordBitIsSet`.

Also checked the existing `lakefile.lean` and migrated `HexArith` /
`HexModArith` files: those libraries use `precompileModules := true` together
with `module` and `@[expose]`, which is local evidence against a blanket
`precompileModules` / `@[expose]` incompatibility.

## Current frontier

The likely fix for `HexGF2` is to promote exactly the private helper
definitions whose bodies must appear in exposed exported definitions, and mark
those helpers `@[expose]` where their own bodies must remain unfoldable across
module boundaries.

## Next step

When implementing the migration, expose the dependency closure of computational
definitions used by exported `rfl`, `simp`, or `decide` proofs, then run
`lake build` and address any remaining diagnostics from the first real error
upward.

## Blockers

None.
