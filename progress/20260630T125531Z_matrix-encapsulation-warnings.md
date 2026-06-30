# Clear Mathlib-free warnings from the Matrix-encapsulation refactor

## Accomplished

After the `Hex.Matrix` encapsulation (it was previously a type alias for
`Vector (Vector R m) n`, now a one-field structure), a batch of linter
warnings appeared in matrix-consuming Mathlib-free code. All resolved; the
files below build with no warnings.

- Dead simp arguments after the normal-form shift: dropped
  `getRow`/`Fin.getElem_fin` from six `simp only` calls and `ih`/`hDone` from
  the `simp_all` calls in `HexBareiss/Bareiss.lean`; `Vector.getElem_*` from
  three `simp_all`/`simp only` calls in `HexMatrix/Elementary.lean`;
  `Hex.Matrix.getRow`/`Fin.getElem_fin` from two `simp` calls in
  `HexGramSchmidt/Int/Combination.lean`; and `if_neg hp` in
  `HexGramSchmidt/Int/Canonical.lean`.
- Unreferenced binders: renamed the now-unused hypothesis `hp` to `_hp` in
  `Canonical.lean` (its only use was the removed `if_neg hp`), and the unused
  `if`-witness `hlt` to `_hlt` in `HexGramSchmidt/Basic/Kernel.lean`
  (`coeffMatrix` is `@[expose]`, so `_hlt` keeps the `dite` term shape rather
  than switching to `ite`).

The kernel-basis manual recipe that the encapsulation also broke was fixed
independently on `main` (#8479, switched to `nullspaceBasisMatrix`), so no
manual change is carried here.

## Current frontier

The Mathlib-free matrix-consumer warnings are cleared. Note that #8475 made
the `*Mathlib` bridge libraries default build targets, which newly surfaces a
separate batch of pre-existing warnings in those bridge layers (deprecations,
`defProp`, unused simp args, unreferenced binders); those are out of scope
for this unit.

## Next step

Decide whether to clear the bridge-layer warning set newly exposed by #8475.

## Blockers

None.
