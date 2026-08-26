# BZ module-system migration — Phase 1a (executable library)

## Accomplished
Migrated the executable `HexBerlekampZassenhaus` library onto the Lean 4
module system (`module` / `public import` / `public section`), as the
prerequisite step before splitting the 19k-line `Basic.lean` monolith.
Whole project builds green (`lake build`, 4088 jobs); `check_dag.py`
passes; no new `sorry`/`axiom`.

The migration surfaced **two genuine lean4 module-system reduction bugs**,
both diagnosed to root and worked around locally:

1. **`Array.instDecidableEqImpl` is not `@[expose]`**, so `decide`/`rfl`
   over `Array` equality does not reduce in the kernel under `module` for
   two nonempty arrays (`instDecidableEq` inlines the empty cases but
   delegates the nonempty case to the opaque impl). Repro + analysis in
   [progress/lean4-array-decidableeq-module-repro.md](lean4-array-decidableeq-module-repro.md).
   - Draft lean4 PR: https://github.com/leanprover/lean4/pull/14270
     (adds `@[expose]`, with a `tests/elab/` regression test).
   - In-tree workaround: `import all Init.Data.Array.DecidableEq` in
     `HexBerlekampZassenhaus/Basic.lean`. The efficient `Array` DecidableEq
     is retained (no switch to a slower `List`-based instance).
2. **`Array.back?` does not reduce under `module`** — reimplemented
   `HexPoly.Euclid.leadingCoeff` as `coeffs.getD (size - 1) 0` instead of
   `coeffs.back?.getD 0` (equal, kernel-reducible, no `Option` alloc).
   Both workarounds carry `-- revert once upstream lands` comments.

Other mechanics: `public meta import`s for the 117 `#guard`s;
`backward.{proofsInPublic,privateInPublic}` for private-in-public;
`@[expose]` on the executable defs that exported `decide`/`rfl`/`unfold`
proofs reduce through (incl. the shallow `factor 0` constant-branch
closure); de-privatised the leaked `GcdLaws Rat` instance; exposed
`SquareFreeRat`. The `leadingCoeff` reimplementation rippled into ~12
`leadingCoeff = coeff (size-1)` re-proofs across HexPoly/HexHensel/
HexBerlekamp/HexPolyFp/HexPolyZ/HexPolyMathlib/HexBZMathlib — all fixed to
`simp [leadingCoeff, coeff, size]` form.

**No runtime performance regression:** the only change to compiled code is
`leadingCoeff` (equal-or-faster); DecidableEq is unchanged (original
efficient instance kept); everything else is compile/elaboration-time.

## Current frontier
Phase 1a green and committable. `HexBerlekampZassenhausMathlib` is still
legacy (only its two `leadingCoeff`-consuming proofs were touched, forced
by the def change).

## Next step
- Phase 1b: migrate `HexBerlekampZassenhausMathlib` (22k, CI-gated) to the
  module system — expect a larger `@[expose]`/private-in-public pass.
- Phase 2: split both `Basic.lean` monoliths into dependency-ordered
  leaves and delete `Basic.lean` (repoint importers to the umbrella).

## Blockers
None. Upstream lean4 PR #14270 pending; the `import all` and `getD`
workarounds keep us green in the meantime.
