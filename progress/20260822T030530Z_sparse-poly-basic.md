# hex-sparse-poly: activation and the representation core

## Accomplished

- Activated `HexSparsePoly` (`libraries.yml` entry with the SPEC's phase4
  comparator/input-family block, `lean_lib`, umbrella) and seeded
  `HexSparsePolyMathlib` as `planned`.
- Moved the SPEC to `HexSparsePoly/SPEC/hex-sparse-poly.md` and rewrote
  its and its referrers' relative links for the new location.
- `HexSparsePoly/Basic.lean`: `SparsePolyCanonical`, `SparsePoly`, the
  hand-written `DecidableEq` over hex-basic's scoped kernel-reducible
  array instance, `Zero`, the accessors (`numTerms`, `isZero`, `support`,
  `degree?`, `leadingCoeff`, `toTerms`, `foldTerms`), `coeff` as the
  `List`-shaped kernel-facing specification with the binary-search
  `coeffImpl` behind a proved `@[csimp]` equality, the linear
  `isCanonical` check deciding `SparsePolyCanonical`, and `ext_coeff`
  via `coeffList_ext`. No `sorry`.

## Current frontier

Milestone 1 of the SPEC is half landed: the representation and its
observation API are in; `addTerm` / `ofTerms` with their `@[csimp]`
twins, `monomial` / `C` / `X`, the `#sp[…]` literal, `coeff_ofTerms`,
and the kernel-exposure probe module are next.

## Next step

`addTerm` as the ordered-`List` insert specification plus the
binary-search/in-place `addTermImpl`, with the invariant-preservation
proof; then `ofTerms` and its stable sort-and-combine twin.

## Blockers

None.
