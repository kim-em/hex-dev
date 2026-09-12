# hex-bareiss-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-bareiss-mathlib` is the Mathlib bridge for
[`hex-bareiss`](https://github.com/leanprover/hex-bareiss). It proves the
row-pivoted Bareiss determinant correct, both against Mathlib's `Matrix.det`
and against the executable Leibniz determinant from
[`hex-determinant`](https://github.com/leanprover/hex-determinant), and it
ships the `det` tactic, which closes determinant equations on closed integer
and rational matrix literals with a kernel-checked certificate. It depends on
[`hex-bareiss`](https://github.com/leanprover/hex-bareiss),
[`hex-determinant-mathlib`](https://github.com/leanprover/hex-determinant-mathlib),
and Mathlib.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-bareiss-mathlib"
git = "https://github.com/leanprover/hex-bareiss-mathlib.git"
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

-- The same correspondence is available over any commutative ring equipped
-- with an exact quotient satisfying the cancellation law.
#check @bareissWith_eq_det
-- @bareissWith_eq_det : ∀ {R n} [CommRing R] [DecidableEq R]
--   (quot : R → R → R), (∀ a b, b ≠ 0 → quot (a * b) b = a) →
--   ∀ M : Hex.Matrix R n n, Matrix.bareissWith quot M = Matrix.det M
#check @bareissWith_eq_mathlib_det
-- @bareissWith_eq_mathlib_det : ∀ {R n} [CommRing R] [DecidableEq R]
--   (quot : R → R → R), (∀ a b, b ≠ 0 → quot (a * b) b = a) →
--   ∀ M : Hex.Matrix R n n,
--     Matrix.bareissWith quot M = (matrixEquiv M).det

-- The `det` tactic closes determinant equations on closed integer and
-- rational literals, in either orientation, with a kernel-checked
-- certificate; `det%` returns the certified value and its proof.
example : Matrix.det (R := ℤ) !![0, 2, 1; 3, 1, 4; 1, 5, 9] = -32 := by det
example : Matrix.det (R := ℚ) !![1 / 2, -1; 3, 5 / 3] = 23 / 6 := by det
#check (det% !![1, 2; 3, 4]).proof
-- (det% !![1, 2; 3, 4]).proof : Matrix.det !![1, 2; 3, 4] = -2

-- `hex_norm_det` is the same certificate as a simproc, with Mathlib's
-- `norm_det` as its fallback for symbolic entries.
example (a b c d : ℤ) : Matrix.det !![a, b; c, d] = a * d - b * c := by
  simp only [hex_norm_det]
  ring
```

# Functionality

- `bareiss_eq_det`: the row-pivoted Bareiss determinant equals the
  executable Leibniz `Hex.Matrix.det`;
- `bareissDet_eq_det` (also `bareiss_eq_mathlib_det`): it equals Mathlib's
  `Matrix.det` of the corresponding matrix `matrixEquiv M`;
- `bareissNoPivot_eq_det` and the bordered-minor invariant
  (`BareissNoPivotInvariant`, `NonzeroBareissPivots`): the Desnanot-Jacobi
  argument that drives the no-pivot correctness proof;
- `bareissWith_eq_det` and `bareissWith_eq_mathlib_det`: the generic
  coefficient-ring correspondence for a supplied exact quotient.
- `det_eq_of_checkList` and `det_eq_of_checkRat`: a passing kernel
  determinant certificate of `hex-bareiss` determines Mathlib's `Matrix.det`
  of an integer or rational matrix given as a row list;
- the `det` tactic, the `det%` term form and the `hex_norm_det` simproc:
  determinants of closed integer and rational literals (`!![…]`,
  `Matrix.of ![…]`, `fun i j => …`, `Matrix.ofArray`), checked in the
  kernel as a triangularization, faster than Mathlib's `eval_det` on every
  shared family, with `norm_det` composed as the fallback.

`Rat` can use the generic correspondence directly. Multivariate polynomials
also have Mathlib ring structures, supplied separately by `HexMvPolyMathlib`.
The executable `ZMod64` and dense-polynomial carriers currently have no global
Mathlib `CommRing` instances: their computational conformance is checked by
value guards and external oracles. Using the generic correspondence at those
carriers also requires that separate bridge work; an exact-division law alone
does not supply the Mathlib ring instance.

# Verification

The correspondence is fully proven over any commutative ring with decidable
equality and a quotient satisfying exact right cancellation. No public domain
or nontriviality hypothesis is required. The original integer theorems remain
the preferred compatibility surface and hold outright.

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
[`hex-bareiss`](https://github.com/leanprover/hex-bareiss); these theorems are on
that Mathlib-free library's forbidden list and live here by design.

# Reference manual

The hex reference manual covers this library and its computational base at
<https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-bareiss>.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
