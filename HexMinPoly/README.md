# hex-min-poly

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-min-poly` computes minimal polynomials of dense square matrices over
fields. It depends on [`hex-matrix`](https://github.com/leanprover/hex-matrix),
[`hex-row-reduce`](https://github.com/leanprover/hex-row-reduce), and
[`hex-poly`](https://github.com/leanprover/hex-poly). The
[`hex-min-poly-mathlib`](https://github.com/leanprover/hex-min-poly-mathlib)
companion identifies its result with Mathlib's minimal polynomial.

# Quickstart

```toml
[[require]]
name = "hex-min-poly"
git = "https://github.com/leanprover/hex-min-poly.git"
rev = "main"
```

```lean
import HexMinPoly

open Hex
open scoped Hex

def A : Matrix Rat 2 2 := #m[0, 1; 0, 0]
def v : Vector Rat 2 := #v[0, 1]

#eval A.vecMinPoly v |>.toArray -- #[0, 0, 1]
#eval A.minPoly.toArray         -- #[0, 0, 1]
#eval (A.minPolyCert.check A)   -- true
```

# Functionality

- `evalVec` applies a dense polynomial in a matrix directly to a vector;
- `krylovRows`, `krylovMat`, and `krylovDeg` expose the Krylov sequence and
  its first dependency;
- `vecMinPoly` computes the monic order polynomial of one vector;
- `minPoly` computes the monic matrix minimal polynomial by a deterministic
  standard-basis sweep;
- `minPolyCert` produces a checkable certificate containing Krylov
  independence and polynomial LCM witnesses.

# Verification

The Mathlib-free layer proves that `vecMinPoly A v` is monic, annihilates
`v`, and divides every other polynomial that annihilates `v`. It proves the
corresponding universal property for `minPoly A` over all vectors. The
certificate checker is sound, and certificates made by `minPolyCert` pass it.

```lean
theorem minPoly_dvd_iff (A : Matrix F n n) (p : DensePoly F) :
    minPoly A ∣ p ↔ ∀ v : Vector F n, evalVec p A v = 0
```

The Mathlib correspondence, divisibility into the characteristic polynomial,
and invariance under transpose and similarity live in
[`hex-min-poly-mathlib`](https://github.com/leanprover/hex-min-poly-mathlib).

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behaviour you want and leave the implementation to the
maintainer.
