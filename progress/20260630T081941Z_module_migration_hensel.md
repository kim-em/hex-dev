# Module migration: Hensel chain (HexHensel, HexHenselMathlib, HexPolyZMathlib)

## Accomplished

Migrated `HexHensel` (Basic/Linear/Multifactor/Quadratic/QuadraticMultifactor/
CrossCheck/umbrella), `HexHenselMathlib` (Basic/Correctness/umbrella), and
`HexPolyZMathlib` (Basic/Mignotte/RobinsonForm/umbrella). Full `lake build`
and `HexConformance` green.

Exposures required by new module consumers:
- In `HexPolyZ` (already a module on main): `@[expose]` added to `congr`,
  `coprimeModP`, `content`, `Primitive` (HexHensel/HexPolyZMathlib `unfold`/
  `rcases`/`simp` them) and `binom` (HexPolyZMathlib.Mignotte unfolds it).
- In `HexHensel`: `@[expose]` on `intModNat`, `polyProduct`,
  `multifactorLiftList`, `multifactorLiftQuadraticList`, `multifactorLift`,
  `multifactorLiftQuadratic`, `MultifactorLiftInvariant`,
  `QuadraticMultifactorLiftInvariant`, `LinearLiftLoopInvariant` (the
  correctness bridge `simp`/`rcases`/`unfold`s these, and the Array-wrapper
  lift defs must unfold to their List forms for the bridge lemma to apply).
- `HexHensel/CrossCheck`: `public meta import` of Multifactor and
  QuadraticMultifactor (`#eval`/`#guard` run those defs at elaboration).
- A few `rfl`/`change` proofs reducing `leadingCoeff 0` rewritten to `simp`.

## Next

Berlekamp chain: `HexBerlekamp` (Risk 1), `HexBerlekampMathlib`, `HexConway`.
Deferred (legacy): `HexGF2`, `HexGF2Mathlib` (Risk-2 codegen), and `HexGFq`,
`HexGFqMathlib` (transitively import legacy `HexGF2`/`HexGF2Mathlib`).
