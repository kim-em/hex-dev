# hex-rank

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-rank` computes the rank of a dense matrix over any nontrivial integral
domain, together with a two-sided certificate that a consumer can re-check
with ring arithmetic and equality tests alone. The producer is rectangular
fraction-free Gauss-Jordan elimination with column pivoting and skipped
columns, which also returns the row and column rank profiles. This library
depends on [`hex-bareiss`](https://github.com/leanprover/hex-bareiss),
[`hex-determinant`](https://github.com/leanprover/hex-determinant),
[`hex-matrix`](https://github.com/leanprover/hex-matrix),
[`hex-arith`](https://github.com/leanprover/hex-arith) and
[`hex-basic`](https://github.com/leanprover/hex-basic). See
[`hex-rank-mathlib`](https://github.com/leanprover/hex-rank-mathlib) for the
correspondence with Mathlib's `Matrix.rank`.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-rank"
git = "https://github.com/leanprover/hex-rank.git"
rev = "main"
```

```lean
import HexRank
import HexMatrix.Notation

open Hex Hex.Matrix

def A : Matrix Int 3 4 := #m[1, 2, 3, 4; 2, 4, 6, 8; 1, 0, 1, 0]

#eval rank A                        -- 2
#eval (rankProfile A).rows          -- pivot rows, in elimination order
#eval (rankProfile A).cols          -- pivot columns, increasing
#eval (rankCert A).denom            -- det of the pivot block, here -2
#eval checkRank A (rankCert A)      -- true

-- The same producer runs over any carrier with an exact quotient.
def Q : Matrix Rat 2 2 := #m[(1 : Rat) / 2, 1 / 3; 1 / 4, 1 / 6]
#eval rankWith Hex.exactDiv Q       -- 1
```

# Functionality

- `RankCert` and `checkRank`: the certificate (an `r × r` submatrix `B` of
  `A` at `rows × cols`, an `adj` and a `denom ≠ 0` with
  `B * adj = denom • 1`) and its checker, which verifies that identity and
  the all-column identity `denom • A = A[·, cols] * (adj * A[rows, ·])`.
  `checkRank` is kernel-reducible on closed inputs, but not cheaply;
- `RankWitness`, `checkRankList` and `rankWitness`: the kernel form of the
  integer certificate, a list-based checker (a modular lower bound, an
  exact upper bound over the non-pivot rows) written for kernel reduction,
  and its producer from `rankCert`. This is what the companion's `rank`
  tactic replays;
- `rowReduceWith`: fraction-free Gauss-Jordan elimination over any
  coefficient type with a caller-supplied exact quotient, returning the rank
  profile, the last pivot (`det` of the pivot block) and the reduced form.
  Compiled code runs the in-place `rowReduceWithImpl` on array row storage,
  registered by `@[csimp]`; the public definition is the kernel-facing one;
- `rankWith`, `rankProfileWith`, `rankCertWith`, `certifyRankWith`: the
  generic entry points, and `rank`, `rankProfile`, `rowReduceFF`,
  `rankCert`, `certifyRank`: their `Int` forms through the GMP-backed exact
  quotient;
- `Hex.DomainLaws` (in `hex-basic`): the nontrivial-domain law package the
  checker's soundness is stated over. Exact division is a producer
  requirement, never a checker requirement.

# Verification

The Mathlib-free layer proves the checker sound over any nontrivial domain:
a checked certificate of rank `r` has a nonzero `r × r` minor and every
`(r + 1) × (r + 1)` minor vanishes, so `r` is the largest size of a nonzero
minor.

```lean
theorem RankCert.det_ne_zero {A : Matrix R n m} {c : RankCert R n m}
    (h : checkRank A c = true) :
    det (selectedSubmatrix A c.rows c.cols) ≠ 0

theorem RankCert.det_succ_eq_zero {A : Matrix R n m} {c : RankCert R n m}
    (h : checkRank A c = true)
    (rows : Vector (Fin n) (c.rank + 1)) (cols : Vector (Fin m) (c.rank + 1)) :
    det (selectedSubmatrix A rows cols) = 0
```

The loop-step lemmas of `rowReduceWith` are structural. That the producer's
certificate checks, that its denominator is the determinant of the pivot
block, and that the certified rank is Mathlib's `Matrix.rank` over the domain
and over any fraction field, are proven in
[`hex-rank-mathlib`](https://github.com/leanprover/hex-rank-mathlib).

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and leave
the implementation to the maintainer.
