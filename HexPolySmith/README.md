# hex-poly-smith

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra library
for Lean 4. `hex-poly-smith` computes Smith normal forms of dense polynomial
matrices over a field. The computational library is Mathlib-free; the
correspondence with Mathlib polynomials, modules, and rational-function rank
lives in
[`hex-poly-smith-mathlib`](https://github.com/leanprover/hex-poly-smith-mathlib).

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-poly-smith"
git = "https://github.com/leanprover/hex-poly-smith.git"
rev = "main"
```

```lean
import HexPolySmith

open Hex Hex.PolyMatrix

def x : DensePoly Rat := DensePoly.ofList [0, 1]

def A : Matrix (DensePoly Rat) 2 2 :=
  #m[x, 0; 0, x * x]

#eval snfRank A                 -- 2
#eval (invariantFactors A).toList
#eval quotientOrder A          -- x^3, in dense coefficient form

-- Ask for the transforms and their explicit inverses when needed.
#eval (snfData A).rank
```

# Functionality

- `snf` computes the canonical diagonal matrix without accumulating
  transformations;
- `snfRank` and `invariantFactors` project its rank and monic divisibility
  chain;
- `snfData` additionally returns left and right transformations and their
  explicit inverses;
- `snfDiagonal` and `snfDiagonalData` are convenience entry points for
  diagonal input using the same certified reduction;
- `moduleStructure` and `quotientOrder` describe the module presented by the
  rows of the input matrix;
- `solve` decides and constructs solutions of `Matrix.vecMul x A = b`;
- `snfCert` checks a full direct certificate, while `mulEqCertAt` checks a
  polynomial matrix product at separating evaluation points.

# Verification

`snfData_isSNF` proves that the returned transformations are inverses, that
their product with the input is the returned diagonal, and that the diagonal
is monic and forms a divisibility chain. Determinantal divisors prove the rank
and invariant factors unique. `solve_sound` and `solve_complete` characterize
the solver, and `snfCert_sound` validates independently supplied certificates.

```lean
theorem snfData_isSNF (A : Matrix (DensePoly F) n m) :
    IsSNF A (snfData A)

theorem solve_sound (h : solve A b = some x) : Matrix.vecMul x A = b

theorem solve_complete (h : ∃ x, Matrix.vecMul x A = b) :
    (solve A b).isSome
```

The committed conformance corpus checks the canonical diagonal independently
with SymPy over `QQ[x]` and finite-field polynomial rings. The benchmark suite
tracks dimension, degree, and rational coefficient growth separately.

# Reference manual

The hex reference manual covers this library at
<https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-poly-smith>.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in the published mirror. Contributions are welcome as pull
requests to the monorepo.
