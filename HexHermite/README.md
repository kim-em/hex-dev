# hex-hermite

Part of [`hex`](https://github.com/leanprover/hex), a computer algebra library
for Lean 4.

`hex-hermite` computes the canonical row Hermite normal form of rectangular
integer matrices. It exposes form-only, transform, and transform-with-inverse
paths, along with integer row-lattice membership, saturated kernel bases,
pivot values, lattice indices, and independently checkable HNF certificates.

# Quickstart

Add `hex-hermite` as a Lake dependency and import the umbrella:

```toml
[[require]]
name = "hex-hermite"
git = "https://github.com/leanprover/hex-hermite.git"
rev = "main"
```

```lean
import HexHermite

open Hex

def A : Matrix Int 3 2 :=
  Matrix.ofFn fun i j => #[#[6, 9], #[4, 7], #[-2, 1]][i.val]![j.val]!

#eval (Matrix.hnf A).rows
#eval Matrix.hnfRank A
#eval (Matrix.hnfData A).transform
#eval Matrix.latticeContains A (Vector.ofFn fun j => if j.val = 0 then 2 else 2)
```

# Functionality

- `hnf`, `hnfRank`, and `hnfBasis` compute the form and its nonzero basis rows.
- `hnfData` returns the unimodular left transform; `hnfWithInv` also accumulates
  its inverse.
- `latticeCoeffs` and `latticeContains` solve integer row-lattice membership.
- `kernelBasis`, `pivots`, and `latticeIndex` expose the derived lattice data.
- `hnfCert` checks externally produced forms and transforms.

# Verification

The Mathlib-free contract `IsHNF` combines the shared row-echelon transform
contract with positive pivots and canonical reduced residues. The executable
shape checker and packed certificate have a proved soundness theorem. The form,
transform, and inverse paths share one deterministic accumulator-parametric
elimination schedule, with proved form/rank/data agreement.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo; released repositories are generated mirrors. Make changes in the
monorepo rather than editing a released repository directly.
