# Module migration Group A: HexPolyMathlib, HexPolyZ (HexGF2 deferred)

## Accomplished

Migrated `HexPolyMathlib` (Basic + Euclid + umbrella) and `HexPolyZ`
(Basic + Mignotte + umbrella) to the module system. Full `lake build` and
`HexConformance` both green (real exit 0).

Exposure/fix details:
- `HexPolyMathlib/Basic`: `@[expose]` on `toPolynomial`/`ofPolynomial`/`equiv`;
  rewrote one `leadingCoeff_toPolynomial` zero-branch `rfl` to
  `simp [DensePoly.coeff_zero]` (the `rfl` reduced through the `DensePoly`
  structure/Zero instance, which a module cannot unfold cross-file).
- `HexPolyZ/Basic`: `@[expose]` on `IsUnit`; made `normalizePrimitiveSign`
  public + `@[expose]` (two public theorems name it in their statements and
  `unfold` it — illegal for a `private` def under the module system); replaced
  two `change 0 < (0 : Int) at h` with `rw [DensePoly.leadingCoeff_zero] at h`
  and one scale-zero `change`+`rfl` block with `simp`.
- `HexPolyZ/Mignotte`: `@[expose]` on `coeffNormSq`, `coeffL2NormBound`,
  `mignotteCoeffBound`, `defaultFactorCoeffBound` (their exported `_def`
  unfolding lemmas).

## HexGF2 deferred (Risk 2 CONFIRMED)

`HexGF2` cannot be migrated: its exported `@[simp]` lemmas (e.g.
`degree?_zero`) are `rfl` proofs that must unfold `ofWords`/`degree?`/`zero`.
Exposing those defs under `precompileModules := true` triggers codegen errors
`"Failed to find LCNF signature for Hex.GF2Poly.ofWords"`,
`"declaration has metavariables"`, and `"failed to compile definition,
consider marking it 'noncomputable'"`. The only alternatives — making the
`@[simp]` lemmas `private` — would break the downstream API that
`HexGF2Mathlib` consumes. This is a genuine Lean toolchain limitation (the
prior sweep also left `HexGF2` legacy); `HexGF2` and `HexGF2Mathlib` stay
legacy.

## Next step

Group B: `HexGFqField`, `HexHensel`(+Mathlib), `HexConway`, `HexGFq`(+Mathlib),
`HexPolyZMathlib`. Then `HexBerlekamp`(+Mathlib) (Risk 1). Each needs the
exported-`rfl` `@[expose]` pass; expect more `private`→public promotions where
public theorem statements name internal defs.

## Blockers

`HexGF2`/`HexGF2Mathlib`: confirmed `@[expose]`+`precompileModules` codegen
blocker (above).
