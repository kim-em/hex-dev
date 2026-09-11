# hex-rank-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-rank-mathlib` is the Mathlib bridge for
[`hex-rank`](https://github.com/leanprover/hex-rank). It proves that a
checked rank certificate determines Mathlib's `Matrix.rank` over the domain
and after any injective ring homomorphism into a domain, that the rank is
unchanged by extension of scalars to a fraction field, and that the producer
`rankCertWith` emits a certificate that checks. It depends on
[`hex-rank`](https://github.com/leanprover/hex-rank),
[`hex-bareiss-mathlib`](https://github.com/leanprover/hex-bareiss-mathlib),
[`hex-determinant-mathlib`](https://github.com/leanprover/hex-determinant-mathlib),
[`hex-matrix-mathlib`](https://github.com/leanprover/hex-matrix-mathlib) and
Mathlib.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-rank-mathlib"
git = "https://github.com/leanprover/hex-rank-mathlib.git"
rev = "main"
```

```lean
import HexRankMathlib

open HexMatrixMathlib

-- A checked certificate determines Mathlib's rank.
#check @checkRank_sound
-- ∀ {R n m} [CommRing R] [IsDomain R] [DecidableEq R] {A c},
--   Hex.Matrix.checkRank A c = true → (matrixEquiv A).rank = c.rank

-- The producer's certificate checks, so the unchecked rank is Mathlib's.
#check @rankCertWith_check
#check @rank_eq_rank
-- ∀ {n m} (A : Hex.Matrix ℤ n m), Hex.Matrix.rank A = (matrixEquiv A).rank

-- Rank is unchanged by passing to any fraction field.
#check @rank_map_eq
```

# Functionality

- `checkRank_sound` and `checkRank_sound_map`: soundness of the checker for
  `Matrix.rank` over the domain, and over any domain reached by an injective
  ring homomorphism;
- `rowReduceWith_spec`: the reduced-form contract of the producer, proved by
  the loop invariant of `HexRankMathlib.Invariant` (the pivot rows are the
  rows of `adjugate B * P`, the denominator is `det B`);
- `rankCertWith_check`, `rankWith_eq`, `rank_eq`: producer correctness and
  the identification of the unchecked rank with `Matrix.rank`;
- `exists_rankCert`: completeness of the certificate shape over every domain;
- `rank_map_eq`, `rank_map_eq_rank_fractionRing`, `rank_eq_ratFunc_rank'`:
  rank invariance under extension of scalars to a fraction field;
- `rowReduceWith_cols_eq_colProfile` and `rowReduceWith_rows_eq_rowProfile`:
  the producer's pivot columns are the column rank profile and its pivot rows
  are, as a set, the row rank profile (`IsColRankProfile`,
  `IsRowRankProfile`);
- a `Decidable (A.rank = r)` instance for integer matrices, run by the
  producer;
- `rank_eq_of_checkList`: soundness of hex-rank's kernel certificate for
  `Matrix.rank` of an integer matrix given as a row list, with `ofLists`
  identifying a `!![…]` literal with its row list definitionally;
- the `rank` tactic: `A.rank = r`, `A.rank ≤ r` and `r ≤ A.rank` for a
  closed integer literal `A`, by the compiled producer and one kernel check
  of the certificate; 6 to 60 times less kernel time than Mathlib's
  `eval_rank` on 8 × 8 to 32 × 32 literals.

# Verification

```lean
theorem checkRank_sound [CommRing R] [IsDomain R] [DecidableEq R]
    {A : Hex.Matrix R n m} {c : Hex.Matrix.RankCert R n m}
    (h : Hex.Matrix.checkRank A c = true) :
    (matrixEquiv A).rank = c.rank

theorem rankCertWith_check (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)
    (h1 : (1 : R) ≠ 0) (A : Hex.Matrix R n m) :
    Hex.Matrix.checkRank A (Hex.Matrix.rankCertWith quot A) = true

theorem rank_map_eq [CommRing R] [IsDomain R] {K : Type v} [Field K] [Algebra R K]
    [IsFractionRing R K] (M : Matrix (Fin n) (Fin m) R) :
    (M.map (algebraMap R K)).rank = M.rank
```

The adapters to Mathlib's `Echelon.Decomposition` named in the SPEC are not
yet provided.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and leave
the implementation to the maintainer.
