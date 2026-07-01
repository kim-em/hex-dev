# Matrix encapsulation: merged onto current main (v432)

## Accomplished

- Finished `HexGramSchmidt/Int/Combination.lean` (the last hard
  Mathlib-free file): restated the `rowSwap_getRow_*_val_int` helpers in
  `getRow` form (so they match the `dsimp`-normalized goal under the
  `getElem_eq_getRow` simp normalization), kept `of_ne` with `Nat`
  conditions but a `getRow ⟨r,hr⟩` LHS, and bumped `maxHeartbeats` on the
  one entry-symmetry proof whose elaboration the structure made slower.
- Removed the `get`/`getRow` duplicate accessor; all consumers use
  `getRow`. (`row := getRow` stays — it is main's pre-existing alias.)
- Migrated `HexLLL`, `HexBerlekamp`, `HexBerlekampZassenhaus`.
- **Re-based onto current `main` by merge (not rebase).** A single 3-way
  merge surfaced only two real conflicts (`HexMatrix/Basic.lean`,
  `HexLLL/Basic.lean`); main's independent refactors (foldl consolidation
  into `HexBasic`, `List.foldl_add_*` renames, the `HexLLL` monolith split
  into modules, `Vector/Modify` relocation to `HexBasic`) came in cleanly.
- Relocated the `Hex.Matrix` row-op block (`modify`/`swap`/`mapRows`) from
  the now-`Matrix`-agnostic `HexBasic/Vector/Modify.lean` into
  `HexMatrix/Basic.lean`.
- Added what main's newer code needs from the structure: a `Mul`-based
  `SMul R (Matrix R n m)` (+ `smul_getElem`) for `#8447`'s `mul_adjugate`
  (`det M • identity`); `deriving DecidableEq, BEq`; and a `Repr` instance
  displaying through `data` so `#eval`/`#guard_msgs` output is unchanged.
- Re-applied the mechanical transforms to the new `HexLLL` split modules
  (`Native`, `Certificate`, `Checker`, `Provider`, `Steered`, `Dispatch`)
  and to `bench/` + `conformance/`.

## Current frontier

Whole tree green on v4.32: `lake build` (2561 jobs), every matrix-family
bench exe, and `HexConformance`. Branch `matrix-encapsulation-v432`
pushed (`d6bb1490`).

## Next step

- Cleanup before merge: the one `maxHeartbeats 1000000` in Combination,
  and any remaining unused-`simp`-arg warnings.
- SPEC updates: HexMatrix opaque-boundary + noncomputable-row-guard
  rationale; HexMatrixMathlib `matrixEquiv` via entry API.
- Open/update the PR against current main.

## Blockers

None.
