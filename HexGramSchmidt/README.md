# hex-gram-schmidt

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-gram-schmidt` provides executable Gram-Schmidt orthogonalization for
integer and rational matrices: the orthogonal basis, the triangular
coefficient matrix, the leading Gram determinants, and the update formulas
under lattice row operations. The integer construction is fraction-free,
running over [`hex-matrix`](https://github.com/kim-em/hex-matrix) and the
Bareiss determinant from [`hex-bareiss`](https://github.com/kim-em/hex-bareiss);
[`hex-determinant`](https://github.com/kim-em/hex-determinant) and
[`hex-row-reduce`](https://github.com/kim-em/hex-row-reduce) complete the
matrix toolkit it builds on. See
[`hex-gram-schmidt-mathlib`](https://github.com/kim-em/hex-gram-schmidt-mathlib)
for the correspondence with Mathlib's `gramSchmidt`.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-gram-schmidt"
git = "https://github.com/kim-em/hex-gram-schmidt.git"
rev = "main"
```

```lean
import HexGramSchmidt

open Hex

-- An integer basis, one lattice generator per row.
def B : Matrix Int 3 3 := Matrix.ofFn fun i j => if i = j then (2 : Int) else 1

-- Leading Gram determinants dₖ and the integer scaled coefficients
-- νᵢⱼ = dⱼ₊₁·μᵢⱼ come from a fraction-free Bareiss pass (no rational division).
#check (GramSchmidt.Int.gramDet B 3 (by decide) : Nat)   -- 16
#check (GramSchmidt.Int.gramDetVec B : Vector Nat 4)     -- #v[1, 6, 11, 16]
#check (GramSchmidt.Int.scaledCoeffs B : Matrix Int 3 3) -- diagonal 6, 11, 16

-- Lattice row operations are plain data transforms.
#eval GramSchmidt.Int.sizeReduce B 0 2 1          -- row 2 ← row 2 − 1·row 0
#eval GramSchmidt.Int.adjacentSwap B 1 (by decide)

-- Rational input goes through GramSchmidt.Rat.
def C : Matrix Rat 2 2 := Matrix.ofFn fun i j => if i = j then ((1 : Rat) / 2) else 0
#check (GramSchmidt.Rat.gramDet C 2 (by decide) : Rat)   -- 1/4
```

# Functionality

The integer construction `GramSchmidt.Int`:

- `gramDet` and `gramDetVec`: the leading principal Gram determinants,
  computed together in one Bareiss pass;
- `scaledCoeffs`: the integer scaled coefficients νᵢⱼ = dⱼ₊₁·μᵢⱼ, with the
  Gram determinants on the diagonal;
- `sizeReduce` and `adjacentSwap`: the lattice row operations, with helpers
  (`adjacentSwapDenom`, `adjacentSwapGramDetQuotient`, and friends) for their
  exact-update formulas.

The rational construction `GramSchmidt.Rat` provides `gramDet`, and the
proof-facing `basis` and `coeffs` (the orthogonal basis and the
lower-unitriangular coefficient matrix) are available over both rings.

# Verification

The orthogonalization theory is proven over the Mathlib-free integer and
rational cores. The orthogonal basis, `basis_orthogonal`:

```lean
theorem basis_orthogonal (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ((basis b).row ⟨i, hi⟩).dotProduct ((basis b).row ⟨j, hj⟩) = 0
```

is accompanied by the triangular decomposition `basis_decomposition`, the
coefficient laws `coeffs_diag` and `coeffs_upper`, the span equality
`basis_span`, and the update laws for `sizeReduce` and `adjacentSwap`. The
key lattice estimate, `normSq_latticeVec_ge_min_basis_normSq`:

```lean
theorem normSq_latticeVec_ge_min_basis_normSq
    (b : Matrix Int n m) (_hli : independent b)
    (v : Vector Int m) (hv : memLattice b v) (hv' : v ≠ 0) :
    ∃ i : Fin n,
      ((basis b).row i).normSq ≤ ((v.normSq : Int) : Rat)
```

bounds every nonzero lattice vector below by a basis norm.

Facts that equate a Hex computational output with the Leibniz `det` of a
matrix go through Bareiss-Desnanot integrality, so they live in
[`hex-gram-schmidt-mathlib`](https://github.com/kim-em/hex-gram-schmidt-mathlib),
along with the correspondence between `GramSchmidt.Int.basis` and Mathlib's
`gramSchmidt`.

# Reference manual

The hex reference manual covers this library at
<https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-gram-schmidt>.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
