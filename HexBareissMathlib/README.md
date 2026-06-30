# hex-bareiss-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-bareiss-mathlib` is the Mathlib bridge for
[`hex-bareiss`](https://github.com/kim-em/hex-bareiss). It proves the
row-pivoted Bareiss determinant correct, both against Mathlib's `Matrix.det`
and against the executable Leibniz determinant from
[`hex-determinant`](https://github.com/kim-em/hex-determinant). It depends on
[`hex-bareiss`](https://github.com/kim-em/hex-bareiss),
[`hex-determinant-mathlib`](https://github.com/kim-em/hex-determinant-mathlib),
and Mathlib.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-bareiss-mathlib"
git = "https://github.com/kim-em/hex-bareiss-mathlib.git"
rev = "main"
```

```lean
import HexBareissMathlib

open HexMatrixMathlib

-- The executable Bareiss determinant equals the Leibniz determinant.
#check @bareiss_eq_det
-- @bareiss_eq_det : ∀ {n : ℕ} (M : Hex.Matrix ℤ n n), M.bareiss = M.det

-- ... and equals Mathlib's determinant of the corresponding matrix.
#check @bareissDet_eq_det
-- @bareissDet_eq_det : ∀ {n : ℕ} (M : Hex.Matrix ℤ n n), M.bareiss = (matrixEquiv M).det
```

# Functionality

- `bareiss_eq_det`: the row-pivoted Bareiss determinant equals the
  executable Leibniz `Hex.Matrix.det`;
- `bareissDet_eq_det` (also `bareiss_eq_mathlib_det`): it equals Mathlib's
  `Matrix.det` of the corresponding matrix `matrixEquiv M`;
- `bareissNoPivot_eq_det` and the bordered-minor invariant
  (`BareissNoPivotInvariant`, `NonzeroBareissPivots`): the Desnanot-Jacobi
  argument that drives the no-pivot correctness proof.

# Verification

The correspondence is fully proven on integer square matrices. The two
headline theorems are the preferred surface for Mathlib-side callers; both
hold outright, with no hypothesis to discharge.

The executable Bareiss determinant equals the Leibniz determinant,
`bareiss_eq_det`:

```lean
theorem bareiss_eq_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Hex.Matrix.det M
```

It also equals Mathlib's determinant, `bareissDet_eq_det`:

```lean
theorem bareissDet_eq_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Matrix.det (matrixEquiv M)
```

The Mathlib statement is proven directly by running the Bareiss loop and
tracking the bordered-minor invariant step by step, `bareiss_eq_mathlib_det`:

```lean
theorem bareiss_eq_mathlib_det (M : Hex.Matrix Int n n) :
    Hex.Matrix.bareiss M = Matrix.det (matrixEquiv M)
```

The executable algorithm itself lives in
[`hex-bareiss`](https://github.com/kim-em/hex-bareiss); these theorems are on
that Mathlib-free library's forbidden list and live here by design.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
