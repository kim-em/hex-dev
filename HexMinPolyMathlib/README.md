# hex-min-poly-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-min-poly-mathlib` is the Mathlib bridge for
[`hex-min-poly`](https://github.com/leanprover/hex-min-poly). It depends on
that computational library, `hex-matrix-mathlib`, `hex-poly-mathlib`,
`hex-char-poly-mathlib`, and Mathlib.

# Quickstart

```toml
[[require]]
name = "hex-min-poly-mathlib"
git = "https://github.com/leanprover/hex-min-poly-mathlib.git"
rev = "main"
```

```lean
import HexMinPolyMathlib

open HexMinPolyMathlib

#check equiv_minPoly
#check vecMinPoly_dvd_iff
#check minPoly_dvd_charPoly
#check minPoly_transpose
#check minPoly_conj
```

# Functionality

- `equiv_minPoly` identifies the executable result with Mathlib's `minpoly`;
- `vectorEquiv_evalVec` transports matrix-polynomial vector evaluation to
  Mathlib's `aeval`;
- `vecMinPoly_dvd_iff` characterizes vector annihilators after conversion;
- `equiv_lcm` identifies executable monic LCM with normalized Mathlib LCM;
- `minPoly_dvd_charPoly` and `degree?_minPoly_le` derive the standard
  characteristic-polynomial bounds;
- `minPoly_transpose` and `minPoly_conj` establish transpose and similarity
  invariance.

# Verification

The bridge is fully proved for matrices over fields with decidable equality.
The central theorem is:

```lean
theorem equiv_minPoly (A : Hex.Matrix F n n) :
    equiv (Hex.Matrix.minPoly A) = minpoly F (matrixEquiv A)
```

The proof uses the executable monicity, annihilation, and divisibility
contracts to invoke Mathlib's uniqueness theorem. The executable algorithm
and its division-free certificate checker remain in
[`hex-min-poly`](https://github.com/leanprover/hex-min-poly).

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behaviour you want and leave the implementation to the
maintainer.
