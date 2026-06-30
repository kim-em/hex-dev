# Module migration: HexGFqField

## Accomplished

Migrated `HexGFqField` (Operations + umbrella; Basic was already a module) to
the module system. Full `lake build` and `HexConformance` green.

Exposure/fixes:
- `@[expose]` on the 15 delegating operation defs in `Operations` (natCast,
  zero, one, add, mul, neg, sub, pow, nsmul, intCast, zsmul, inv, div, zpow,
  frob) so the exported `toQuotient_*`/`repr_*` `rfl` simp lemmas reduce
  through them (the `FiniteField` structure projection reduces by iota once
  the constructor-producing ops are exposed; the structure itself cannot take
  `@[expose]`).
- `invPoly`: `private` -> public + `@[expose]` (the exposed `inv` references
  it, and `inv_zero`'s `change` unfolds it).
- `inv_one`, `inv_inv`, `inv_inv_def`, `pow_zero_eq_one`: `private` -> public.
  The module system does not resolve `private` sibling theorems from inside a
  `public` declaration's proof (the `Grind.Field`/`HPow` instances), so helper
  theorems used by public instances must themselves be public.

## Next

Remaining Group B: `HexHensel`(+Mathlib), `HexConway`, `HexGFq`(+Mathlib),
`HexPolyZMathlib` (the last depends on Group A's `HexPolyZ`/`HexPolyMathlib`).
Then `HexBerlekamp`(+Mathlib) (Risk 1).
