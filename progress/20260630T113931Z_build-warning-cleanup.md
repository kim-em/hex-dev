# Build warning cleanup (non-module-system)

## Accomplished

Cleared every non-sorry build warning that is not tied to the in-progress
module-system migration. Full `lake build` is green; the only remaining
warnings are the `backward.privateInPublic` set (deliberately left for the
module-system work) and warnings inside the `verso`/`subverso` dependencies.

- `linter.defProp` (`def` of a `Prop` → `theorem`): converted `primeTwo` in
  `HexBerlekamp/Irreducibility.lean` and `HexGFq/CrossCheck.lean`, and
  `HexModArith.primeModulusOfPrime`. The latter carried `@[expose, reducible]`
  (which only apply to `def`); dropping both is sound because `PrimeModulus`
  is a `Prop`, so proof irrelevance makes reducibility/exposure of the witness
  irrelevant at use sites. Added `omit [Bounds p] in` to silence the now-unused
  auto-included section instance.
- Deprecation: `Polynomial.finset_sum_coeff` → `Polynomial.finsetSum_coeff`
  in `HexPolyMathlib/Basic.lean`.
- `HexGF2Mathlib/Basic.lean` tactic-linter warnings: dropped a dead
  `<;> decide`, dropped an unused `Nat.lt_succ_self` simp arg, dropped unused
  `ZMod64.toNat_mul` / `ZMod64.toNat_add` simp-only args, and split a
  `... <;> grind` (`unnecessarySeqFocus`) into a sequenced `grind`.

## Current frontier

Tree builds green. Remaining warnings are all the module-system
`privateInPublic` set or warnings inside third-party deps (`verso`,
`subverso`).

## Next step

The `privateInPublic` warnings want the module-system migration finished
(make the referenced helper decls public, drop
`set_option backward.privateInPublic true`).

## Blockers

None.
