# Mark kernel-facing `@[csimp]` specs `noncomputable`

## Accomplished

- Established empirically that a `noncomputable` spec with a proved
  `@[csimp]` twin is fully viable: the spec still kernel-reduces for
  `decide` (`noncomputable` suppresses only code generation), compiled
  callers are redirected to the `*Impl` by csimp, and this holds through
  transitive callers and the polymorphic typeclass signatures used here.
  This keeps the proof-carrying csimp guarantee (unlike the forbidden
  `@[implemented_by]`) while no longer emitting the slow reference body
  as dead compiled code.
- Marked all eight kernel-facing `@[csimp]` specs `noncomputable`:
  `ZMod64.add`/`sub` (HexModArith), `Vector.dotProduct` /
  `Matrix.mul` (HexMatrix), `DensePoly.mul` (HexPoly.Operations),
  `Nat.choose` (HexArith.Nat.Prime), `divModArrayAux`
  (HexPoly.Euclid.DivGcd), `trimTrailingZeros` (HexPoly.Dense). The
  `*Impl` twins stay computable.
- Updated design principle 11 (SPEC/design-principles.md) to mandate the
  `noncomputable` spec and refreshed its precedent list.
- Verified: full `lake build` green (4142 jobs); `HexConformance` and the
  bench exes build green; `hexmatrix_bench` / `hexmodarith_bench` /
  `hexarith_bench` verify pass; `hexpoly_bench` non-Flint benchmarks all
  pass (the 44 Flint failures are environmental -- `python-flint` is not
  installed here -- not from this change).

## Current frontier

- Change confined to 8 spec defs + principle 11. Ready for second opinion
  and PR.

## Next step

- Second opinion, then PR against `main`; branch
  `noncomputable-csimp-specs`.

## Blockers

- None.
