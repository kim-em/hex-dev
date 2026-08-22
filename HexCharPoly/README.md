# hex-char-poly

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra library
for Lean 4.

`hex-char-poly` provides a Mathlib-free, executable characteristic polynomial
for dense square matrices over any commutative ring.  It uses the
division-free Samuelson--Berkowitz algorithm and returns
`det (x·I − A)` as an ascending-coefficient `Hex.DensePoly`.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-char-poly"
git = "https://github.com/leanprover/hex-char-poly.git"
rev = "main"
```

```lean
import HexCharPoly

def A : Hex.Matrix Int 2 2 :=
  Hex.Matrix.ofFn fun i j => #[#[1, 2], #[3, 4]][i.val]![j.val]!

#eval A.charPoly.toArray -- #[-2, -5, 1]
#eval A.trace            -- 5
```

# Functionality

- `Hex.Matrix.charPoly` computes `det (x·I − A)` without division;
- `berkowitz`, `berkowitzStep`, and `berkowitzColumn` expose the descending
  coefficient recursion;
- `trace` sums diagonal entries;
- `evalMatrix` evaluates a dense polynomial at a square matrix by Horner's
  method;
- closed forms cover dimensions zero, one, and two.

# Verification

The Mathlib-free layer proves that the result is monic, has the expected size
and degree over a nontrivial ring, has coefficient `−trace A` at degree
`n - 1`, and has the specified closed forms in dimensions zero through two.
The companion
[`hex-char-poly-mathlib`](https://github.com/leanprover/hex-char-poly-mathlib)
proves correspondence with Mathlib's `Matrix.charpoly` and Cayley--Hamilton.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo; this repository is a
published mirror. Contributions should be opened against the monorepo.
