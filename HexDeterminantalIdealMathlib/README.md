# hex-determinantal-ideal-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-determinantal-ideal-mathlib` is the Mathlib companion for
[`hex-determinantal-ideal`](https://github.com/leanprover/hex-determinantal-ideal).
It identifies the executable minors with `Matrix.det` of a `submatrix`,
states the rank-versus-minors theorem for `Matrix.rank` under an arbitrary
ring homomorphism into a field, reads the rank-drop locus of a polynomial
matrix as `MvPolynomial.zeroLocus` of the determinantal ideal, and proves
that `Ideal.span` of the minors is unchanged by invertible row and column
operations. It depends on
[`hex-determinantal-ideal`](https://github.com/leanprover/hex-determinantal-ideal),
[`hex-determinant-mathlib`](https://github.com/leanprover/hex-determinant-mathlib),
[`hex-row-reduce-mathlib`](https://github.com/leanprover/hex-row-reduce-mathlib),
[`hex-mv-poly-mathlib`](https://github.com/leanprover/hex-mv-poly-mathlib),
and Mathlib.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-determinantal-ideal-mathlib"
git = "https://github.com/leanprover/hex-determinantal-ideal-mathlib.git"
rev = "main"
```

```lean
import HexDeterminantalIdealMathlib

open HexDeterminantalIdealMathlib

-- `Matrix.rank` is below `r` exactly when every `r × r` minor maps to zero.
#check @rank_lt_iff_minors_map_eq_zero

-- The rank of a polynomial matrix at a point drops exactly on the locus.
#check @rankAt_lt_iff_inLocus

-- That locus is the zero set of the determinantal ideal.
#check @mem_zeroLocus_iff_rank_lt
```

# Functionality

The library transports the executable minors of a `Hex.Matrix R n m` to
Mathlib's function-based matrix `matrixEquiv A`, then states the
correspondence theorems:

- `matrixEquiv_map` and `matrixEquiv_selectedSubmatrix`: an entrywise map and
  a selected submatrix transport to `Matrix.map` and `Matrix.submatrix`;
- `det_selectedSubmatrix_eq`: an executable minor is the Mathlib determinant
  of the corresponding `submatrix`;
- `map_minors`: a ring homomorphism passes through the whole enumeration,
  which is the only place a homomorphism property is used;
- `rank_lt_iff_minors_map_eq_zero` and its corollaries
  `le_rank_iff_exists_minor_map_ne_zero` and
  `rank_le_iff_minors_succ_map_eq_zero`: the rank-versus-minors theorem for
  `Matrix.rank`, and `Matrix.rank_lt_iff_minors_eq_zero'` for a consumer
  holding a Mathlib matrix;
- `rank_map_le_rank_fractionRing`: no specialisation has rank above the
  generic rank;
- `rankAt_lt_iff_inLocus` and `mem_zeroLocus_iff_rank_lt`: the rank-drop
  locus of a polynomial matrix as `MvPolynomial.zeroLocus` of `I_r(A)`;
- `span_detIdealGens_eq`, `span_minors_zero`, `span_minors_eq_bot_of_lt`,
  `span_minors_succ_le` and `span_minors_transpose`: the ideal `I_r(A)`, its
  boundary values, and the descending chain;
- `span_minors_mul_left_le`, `span_minors_mul_right_le`,
  `span_minors_mul_left_eq` and `span_minors_mul_right_eq`: `I_r` is an
  invariant of the matrix under invertible row and column operations.

# Verification

The correspondence is fully proven. The headline theorem holds for every
`RingHom` out of the coefficient ring into a field, so evaluation of
polynomials, reduction modulo a prime and the inclusion of a domain into its
fraction field are all instances of one statement.

Rank versus minors, `rank_lt_iff_minors_map_eq_zero`:

```lean
theorem rank_lt_iff_minors_map_eq_zero [CommRing R] [Field K] (φ : R →+* K)
    (A : Hex.Matrix R n m) (r : Nat) :
    ((matrixEquiv A).map φ).rank < r ↔ ∀ M ∈ Hex.Matrix.minors r A, φ M = 0
```

The rank-drop locus, `rankAt_lt_iff_inLocus` and `mem_zeroLocus_iff_rank_lt`:

```lean
theorem rankAt_lt_iff_inLocus (A : Hex.Matrix (MvPoly k F cmp) n m)
    (p : Fin k → F) (r : Nat) :
    Hex.Matrix.rankAt A p < r ↔ Hex.Matrix.InLocus r A p

theorem mem_zeroLocus_iff_rank_lt (A : Hex.Matrix (MvPoly k F cmp) n m)
    (p : Fin k → F) (r : Nat) :
    p ∈ MvPolynomial.zeroLocus F
        (Ideal.span (HexMvPolyMathlib.equiv '' {M | M ∈ Hex.Matrix.minors r A})) ↔
      ((matrixEquiv A).map (HexMvPolyMathlib.aeval p)).rank < r
```

Both are the headline theorem read through
`HexMvPolyMathlib.aeval p`, the executable evaluation as an `AlgHom`, whose
underlying function is the `MvPoly.eval p` that `rankAt` and `InLocus` are
defined by.

Invariance of the determinantal ideal, `span_minors_mul_left_eq`:

```lean
theorem span_minors_mul_left_eq [CommRing R] (P Pinv : Hex.Matrix R n n)
    (h : Pinv * P = Hex.Matrix.identity n) (A : Hex.Matrix R n m) (r : Nat) :
    Ideal.span {x | x ∈ Hex.Matrix.minors r (P * A)} =
      Ideal.span {x | x ∈ Hex.Matrix.minors r A}
```

A one-sided inverse is enough, because `Hex.Matrix.mul_eq_one_comm` makes it
two-sided. These theorems say that `I_r` is an invariant of the matrix under
invertible row and column operations. They do **not** say that `I_r` is an
invariant of the module a matrix presents: that presentation independence is
the Fitting-ideal theorem, which this library does not prove and Mathlib does
not contain.

The executable minors and the Mathlib-free proof of the rank theorem live in
[`hex-determinantal-ideal`](https://github.com/leanprover/hex-determinantal-ideal).

# Reference manual

The hex reference manual covers this library and its computational base at
<https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-determinantal-ideal>.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
