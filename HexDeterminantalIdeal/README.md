# hex-determinantal-ideal

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-determinantal-ideal` enumerates the `r × r` minors of a matrix over a
commutative ring, presents the `r`-th determinantal ideal `I_r(A)` by a
generating list, and proves that a matrix over a field has rank below `r`
exactly when every `r × r` minor vanishes. Read at a point of a matrix of
multivariate polynomials, that theorem says where the rank of the
specialisation drops: the zero set of `I_r(A)`. This library depends on
[`hex-basic`](https://github.com/leanprover/hex-basic),
[`hex-arith`](https://github.com/leanprover/hex-arith),
[`hex-matrix`](https://github.com/leanprover/hex-matrix),
[`hex-determinant`](https://github.com/leanprover/hex-determinant),
[`hex-row-reduce`](https://github.com/leanprover/hex-row-reduce) and
[`hex-mv-poly`](https://github.com/leanprover/hex-mv-poly). See
[`hex-determinantal-ideal-mathlib`](https://github.com/leanprover/hex-determinantal-ideal-mathlib)
for the correspondence with Mathlib's types and theory.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-determinantal-ideal"
git = "https://github.com/leanprover/hex-determinantal-ideal.git"
rev = "main"
```

```lean
import HexDeterminantalIdeal

open Hex

-- The 2×3 matrix [[1, 2, 3], [4, 5, 6]], of rank 2.
def M : Matrix Int 2 3 := Matrix.ofFn fun i j => (3 * i.val + j.val + 1 : Int)

#eval Hex.Matrix.minors 2 M         -- [-3, -6, -3], the three 2×2 minors
#eval Hex.Matrix.detIdealGens 2 M   -- [-3, -6], generators of I_2(M)

#eval Hex.Matrix.minors 0 M         -- [1], the unit ideal
#eval Hex.Matrix.minors 3 M         -- [], the zero ideal
```

# Functionality

- `minors r A`: every `r × r` minor of `A`, the determinant of
  `selectedSubmatrix A rows cols` for strictly increasing `rows` and `cols`,
  rows outer and columns inner, both in the colexicographic order of
  `selectedColumnTuples`;
- `detIdealGens r A`: the same list with the zeros and the exact duplicates
  dropped, a generating list for `I_r(A)`;
- `specialize A p`: a matrix of multivariate polynomials evaluated entrywise
  at a point `p`;
- `rankAt A p`: the rank of that specialisation, by row reduction over the
  field;
- `InLocus r A p`: the decidable proposition that `p` lies in the zero set of
  `I_r(A)`, that is, that every `r × r` minor of `A` vanishes at `p`.

The conventions at the boundaries come from the definitions rather than from
special cases: `minors 0 A = [1]`, so `I_0(A)` is the unit ideal, and
`minors r A = []` once `r` exceeds a dimension, so `I_r(A)` is the zero
ideal. Everything is `@[expose]`d, so `decide +kernel` evaluates it on closed
inputs.

# Verification

Over a field the rank-versus-minors theorem is fully proven, Mathlib-free,
with `rowReduce_rank` from
[`hex-row-reduce`](https://github.com/leanprover/hex-row-reduce) as the rank.
The headline theorem, `rank_lt_iff_minors_eq_zero`:

```lean
theorem rank_lt_iff_minors_eq_zero (A : Matrix K n m) (r : Nat) :
    rowReduce_rank A < r ↔ ∀ M ∈ minors r A, M = 0
```

Its three corollaries name the forms a consumer asks for,
`le_rank_iff_exists_minor_ne_zero`, `rank_le_iff_minors_succ_eq_zero` and
`rank_eq_iff_minors`:

```lean
theorem le_rank_iff_exists_minor_ne_zero (A : Matrix K n m) (r : Nat) :
    r ≤ rowReduce_rank A ↔ ∃ M ∈ minors r A, M ≠ 0

theorem rank_le_iff_minors_succ_eq_zero (A : Matrix K n m) (r : Nat) :
    rowReduce_rank A ≤ r ↔ ∀ M ∈ minors (r + 1) A, M = 0

theorem rank_eq_iff_minors (A : Matrix K n m) (r : Nat) :
    rowReduce_rank A = r ↔
      (∃ M ∈ minors r A, M ≠ 0) ∧ ∀ M ∈ minors (r + 1) A, M = 0
```

The proof runs through the row-reduced echelon certificate
`rowReduce_isRowReduced`, rectangular Cauchy-Binet, and the Laplace expansion
along a column for the descent from one minor size to the next. No boundary
case is treated separately.

The enumeration itself is characterised by `mem_minors_iff`, counted by
`length_minors` (`n.choose r * m.choose r`), and related to the transpose by
`minors_transpose`, a permutation rather than an equality because the
transpose swaps the outer and inner loops:

```lean
theorem mem_minors_iff (A : Matrix R n m) (r : Nat) (x : R) :
    x ∈ minors r A ↔ ∃ rows ∈ selectedColumnTuples r n,
      ∃ cols ∈ selectedColumnTuples r m,
        x = det (selectedSubmatrix A rows cols)

theorem minors_transpose (A : Matrix R n m) (r : Nat) :
    (minors r A.transpose).Perm (minors r A)
```

Invariance under multiplication is Cauchy-Binet with the factors named,
`minor_mul_left_expand` and its right-handed twin: every `r × r` minor of
`P * A` is a linear combination of `r × r` minors of `A`, which is the
Mathlib-free content of `I_r(P * A) ⊆ I_r(A)`.

```lean
theorem minor_mul_left_expand (P : Matrix R q n) (A : Matrix R n m)
    (rows : Vector (Fin q) r) (cols : Vector (Fin m) r) :
    det (selectedSubmatrix (P * A) rows cols) =
      (selectedColumnTuples r n).foldl (fun acc middle => acc +
        det (selectedSubmatrix A middle cols) *
          det (selectedSubmatrix P rows middle)) 0
```

The statements about `Ideal.span`, the rank-drop locus as a zero set, and the
identification with Mathlib's `Matrix.rank` live in
[`hex-determinantal-ideal-mathlib`](https://github.com/leanprover/hex-determinantal-ideal-mathlib).

# Reference manual

The hex reference manual covers this library at
<https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-determinantal-ideal>.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
