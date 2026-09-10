# hex-determinantal-ideal-mathlib

Correspondence between the executable minors of
[hex-determinantal-ideal](hex-determinantal-ideal.md) and Mathlib's
`Matrix.det` of a `submatrix`, and the rank-versus-minors theorem stated for
`Matrix.rank` under an arbitrary ring homomorphism into a field.
Dependencies are `HexDeterminantalIdeal`, `HexDeterminantMathlib`,
`HexRowReduceMathlib` and `HexMvPolyMathlib`, plus Mathlib. The
computational contracts, the conventions at `r = 0` and `r > min n m`, and
the Mathlib-free proof route are in the computational SPEC and are not
restated here.

This library is `correspondence_only: true`, with comparator absence class
**correspondence-only-layer**. It owns no runtime search, conformance
driver or benchmark process. Build-only examples live in
`HexDeterminantalIdealMathlib/Tests.lean`.

Computational conformance owner: `HexDeterminantalIdeal`.

Computational performance owner: `HexDeterminantalIdeal`.

## Transport

Over `[CommRing R]`, with `matrixEquiv` from `HexMatrixMathlib` and
`det_eq` from `HexDeterminantMathlib`:

```lean
theorem matrixEquiv_map (A : Hex.Matrix R n m) (f : R → S) :
    matrixEquiv (A.map f) = (matrixEquiv A).map f
theorem matrixEquiv_selectedSubmatrix (A : Hex.Matrix R n m)
    (rows : Vector (Fin n) k) (cols : Vector (Fin m) k) :
    matrixEquiv (Hex.Matrix.selectedSubmatrix A rows cols) =
      (matrixEquiv A).submatrix rows.get cols.get
theorem det_selectedSubmatrix_eq (A : Hex.Matrix R n m) (rows cols) :
    Hex.Matrix.det (Hex.Matrix.selectedSubmatrix A rows cols) =
      ((matrixEquiv A).submatrix rows.get cols.get).det
theorem map_minors [CommRing S] (φ : R →+* S) (A : Hex.Matrix R n m) (r : Nat) :
    (Hex.Matrix.minors r A).map φ = Hex.Matrix.minors r (A.map φ)
```

`map_minors` is `RingHom.map_det` read through `det_selectedSubmatrix_eq`
and `matrixEquiv_map`, applied to each member of the enumeration. It is the
only place a homomorphism property of `φ` is used, so the headline theorem
below holds for every `RingHom`, including evaluation of polynomials,
reduction modulo a prime and the inclusion of a domain into its fraction
field.

## The headline theorem

Over `[CommRing R]`, `[Field K]`, `φ : R →+* K`:

```lean
theorem rank_lt_iff_minors_map_eq_zero (A : Hex.Matrix R n m) (r : Nat) :
    ((matrixEquiv A).map φ).rank < r ↔ ∀ M ∈ Hex.Matrix.minors r A, φ M = 0
theorem le_rank_iff_exists_minor_map_ne_zero (A : Hex.Matrix R n m) (r : Nat) :
    r ≤ ((matrixEquiv A).map φ).rank ↔ ∃ M ∈ Hex.Matrix.minors r A, φ M ≠ 0
theorem rank_le_iff_minors_succ_map_eq_zero (A : Hex.Matrix R n m) (r : Nat) :
    ((matrixEquiv A).map φ).rank ≤ r ↔ ∀ M ∈ Hex.Matrix.minors (r + 1) A, φ M = 0
```

Proof: `matrixEquiv_map` rewrites the left side as the rank of
`matrixEquiv (A.map φ)`; `HexRowReduceMathlib.rank_eq` applied to
`rowReduce_isRowReduced (A.map φ)` replaces `Matrix.rank` by
`rowReduce_rank (A.map φ)`, using `Field.toGrindField` for the
`Lean.Grind.Field K` instance `rowReduce` needs and `Classical.decEq` for
`DecidableEq K`; the computational `rank_lt_iff_minors_eq_zero` then
applies, and `map_minors` moves `φ` back onto the minors of `A`. The
boundary cases need no separate treatment: for `r = 0` both sides are
false (`φ 1 = 1 ≠ 0`), and for `r > min n m` both sides are true.

The statement deliberately uses `(matrixEquiv A).map φ` rather than
`matrixEquiv (A.map φ)`, so that a consumer holding a Mathlib matrix
`B : Matrix (Fin n) (Fin m) K` and a factorisation `B = (matrixEquiv A).map φ`
rewrites once. The specialisation `φ = RingHom.id K` gives the field case:

```lean
theorem rank_lt_iff_minors_eq_zero [Field K] (A : Hex.Matrix K n m) (r : Nat) :
    (matrixEquiv A).rank < r ↔ ∀ M ∈ Hex.Matrix.minors r A, M = 0
```

The same statement for a Mathlib matrix `B : Matrix (Fin n) (Fin m) R` is
obtained by `A := matrixEquiv.symm B` and `Equiv.apply_symm_apply`; the
library states that form too, as `Matrix.rank_lt_iff_minors_eq_zero'`, so
the tactic does not re-derive it.

## Specialisation bounds and rank loci

```lean
theorem rank_map_le_rank_fractionRing [IsDomain R] (φ : R →+* K) (A : Hex.Matrix R n m) :
    ((matrixEquiv A).map φ).rank ≤
      ((matrixEquiv A).map (algebraMap R (FractionRing R))).rank
```

Proof: by `le_rank_iff_exists_minor_map_ne_zero` twice. A nonzero
`φ M` forces `M ≠ 0`, and `algebraMap R (FractionRing R)` is injective on a
domain, so `algebraMap M ≠ 0`. This is the statement "no specialisation has
rank above the generic rank". The generic rank itself is computed
elsewhere (`hex-rank`, or `HexPolySmith.snfRank` with
`rank_eq_ratFunc_rank` over `F[x]`) and enters only as the right side.

For polynomial matrices, over `[Field F]`, `A : Hex.Matrix (MvPoly k F cmp) n m`
and a point `p : Vector F k`:

```lean
theorem rankAt_lt_iff_inLocus (A) (p) (r : Nat) :
    Hex.Matrix.rankAt A p < r ↔ Hex.Matrix.InLocus r A p
theorem mem_zeroLocus_iff_rank_lt (A) (p : Fin k → F) (r : Nat) :
    p ∈ MvPolynomial.zeroLocus F
        (Ideal.span (HexMvPolyMathlib.equiv '' {M | M ∈ Hex.Matrix.minors r A})) ↔
      ((matrixEquiv A).map (HexMvPolyMathlib.aevalMathlib p)).rank < r
```

Both are the headline theorem with `φ` the evaluation homomorphism at `p`.
`HexMvPolyMathlib.aeval_eq_eval` identifies the executable `MvPoly.eval p`
with `MvPolynomial.aeval p` composed with `HexMvPolyMathlib.equiv`, which
is how `rankAt` and `InLocus`, defined through `MvPoly.eval`, meet the
ring-homomorphism hypothesis. `mem_zeroLocus_iff_rank_lt` uses
`MvPolynomial.zeroLocus` from `Mathlib/RingTheory/Nullstellensatz.lean`,
whose membership condition `∀ q ∈ I, aeval p q = 0` reduces to the
generators by `Ideal.span_induction`.

## Ideals and invariance

Over `[CommRing R]`, writing `I_r(A)` for
`Ideal.span {x | x ∈ Hex.Matrix.minors r A}`:

```lean
theorem span_detIdealGens_eq [DecidableEq R] (A) (r) :
    Ideal.span {x | x ∈ Hex.Matrix.detIdealGens r A} = I_r(A)
theorem span_minors_zero (A) : I_0(A) = ⊤
theorem span_minors_eq_bot_of_lt (A) (h : n < r ∨ m < r) : I_r(A) = ⊥
theorem span_minors_succ_le (A) (r) : I_(r+1)(A) ≤ I_r(A)
theorem span_minors_transpose (A) (r) : I_r(Aᵀ) = I_r(A)
theorem span_minors_mul_left_le (P : Hex.Matrix R q n) (A) (r) : I_r(P * A) ≤ I_r(A)
theorem span_minors_mul_right_le (A) (Q : Hex.Matrix R m q) (r) : I_r(A * Q) ≤ I_r(A)
theorem span_minors_mul_left_eq (P Pinv : Hex.Matrix R n n) (h : Pinv * P = identity n) (A) (r) :
    I_r(P * A) = I_r(A)
theorem span_minors_mul_right_eq (Q Qinv : Hex.Matrix R m m) (h : Q * Qinv = identity m) (A) (r) :
    I_r(A * Q) = I_r(A)
```

`span_minors_mul_left_le` is `minor_mul_left_expand` read as ideal
membership: each minor of `P * A` is a finite sum of products with minors
of `A`. `span_minors_succ_le` is the Laplace expansion
`det_eq_foldl_laplace_col` together with `deleteRowCol_selectedSubmatrix`.
The equalities follow from the two inequalities applied to `P * A` and
`Pinv * (P * A) = A`. A one-sided inverse suffices because
`Hex.Matrix.mul_eq_one_comm` makes it two-sided.

These theorems say that `I_r` is an invariant of the matrix under
invertible row and column operations. They do **not** say that `I_r` is an
invariant of the module a matrix presents: two presentation matrices of
the same module can have different shapes and are not related by
invertible square factors alone. That presentation independence is the
Fitting-ideal theorem, which this library does not prove and the pinned
Mathlib does not contain.

## Tests

`HexDeterminantalIdealMathlib/Tests.lean`, build-only, no runtime checks:

- `rank_lt_iff_minors_map_eq_zero` on a closed `Hex.Matrix ℤ 2 3` through
  `Int.castRingHom ℚ`, both at `r = 2` (nonzero minor, rank `2`) and at
  `r = 3` (empty list, rank below `3`), with the minors evaluated by
  `decide +kernel` on the Hex side and the rank rewritten through the
  theorem;
- `rankAt_lt_iff_inLocus` on the `2 × 2` Vandermonde matrix in two
  indeterminates over `ℚ`, at `(1, 1)` (in the locus at `r = 2`) and at
  `(1, 2)` (not in the locus);
- `span_minors_mul_left_eq` on a `2 × 2` unimodular `P` and a closed `A`,
  to check that the hypotheses are stated in the form a consumer has.
