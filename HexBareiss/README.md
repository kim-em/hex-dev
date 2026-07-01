# hex-bareiss

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-bareiss` provides the executable fraction-free Bareiss determinant of a
dense integer matrix, computed by Gaussian elimination with exact division.
This library depends on [`hex-determinant`](https://github.com/kim-em/hex-determinant)
and [`hex-matrix`](https://github.com/kim-em/hex-matrix). See
[`hex-bareiss-mathlib`](https://github.com/kim-em/hex-bareiss-mathlib) for the
correspondence with the Leibniz determinant and Mathlib's theory.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-bareiss"
git = "https://github.com/kim-em/hex-bareiss.git"
rev = "main"
```

```lean
import HexBareiss

open Hex

-- A 3×3 integer matrix with a zero leading pivot, forcing a row swap.
def M : Matrix Int 3 3 := Matrix.ofFn fun i j => (i + 2 * j : Int)

#eval Matrix.bareiss M                       -- fraction-free determinant
#eval Matrix.bareiss (Matrix.identity (R := Int) 4)    -- 1

-- bareissData also records the row-swap count alongside the determinant.
#eval (Matrix.bareissData M).det
#eval (Matrix.bareissData M).rowSwaps
```

# Functionality

- `bareiss`: the determinant of a square `Int` matrix via fraction-free
  Gaussian elimination with row pivoting;
- `bareissData`: the same elimination, packaged as a `BareissData` record that
  carries the terminal matrix, the row-swap count, and any singular step, with
  `.det` reading off the signed determinant;
- `bareissNoPivot` and `bareissNoPivotData`: the recurrence without pivot
  search, for inputs whose leading pivots are already nonzero;
- `borderedMinor`: the bordered minors that the correctness development uses to
  track the elimination invariant.

The division at each step is `Int.divExact` (GMP-backed `mpz_divexact`), which
is always exact and carries its divisibility proof.

# Verification

The Mathlib-free layer proves the structural properties of the algorithm: the
exactness of each division, the sign contributed by row swaps, the bordered-minor
entry formulas, and the agreement between the public `bareiss` value and the
determinant encoded by `bareissData`.

The public determinant agrees with the encoded data, `bareiss_eq_bareissData_det`:

```lean
theorem bareiss_eq_bareissData_det (M : Matrix Int n n) :
    bareiss M = (bareissData M).det
```

The no-pivot run, when it reaches the final pivot without a singular step,
reads off the last diagonal entry, `bareiss_eq_noPivotLoop_last_of_no_singular`:

```lean
theorem bareiss_eq_noPivotLoop_last_of_no_singular {k : Nat}
    (M : Matrix Int (k + 1) (k + 1))
    (h_no_sing :
      (noPivotLoop k (noPivotInitialState M)).singularStep = none) :
    bareiss M =
      (noPivotLoop k (noPivotInitialState M)).matrix[Fin.last k][Fin.last k]
```

The correspondence of the Bareiss determinant with the Leibniz
[`det`](https://github.com/kim-em/hex-determinant), via the Desnanot-Jacobi
invariant, is proven in
[`hex-bareiss-mathlib`](https://github.com/kim-em/hex-bareiss-mathlib), not here.

# Reference manual

The hex reference manual covers this library at
<https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-bareiss>.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and leave
the implementation to the maintainer.
