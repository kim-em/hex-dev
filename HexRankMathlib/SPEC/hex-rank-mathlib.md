# hex-rank-mathlib

Correspondence between the executable rank certificate of
[hex-rank](../../HexRank/SPEC/hex-rank.md) and Mathlib's `Matrix.rank`: a checked certificate
determines the rank over the domain itself, the rank is unchanged by
extension of scalars to any fraction field (`IsFractionRing`), the
producer's certificate checks, the producer's index sets are the row and
column rank profiles, and a Hex certificate and a Mathlib
`Echelon.Decomposition` each determine the other. The kernel certificate
of hex-rank determines the rank of a Mathlib integer matrix given as a
row list, and the `rank` tactic closes rank equalities and inequalities
on closed integer literals with it. Dependencies are `HexRank`,
`HexBareissMathlib`, `HexDeterminantMathlib` and `HexMatrixMathlib`, plus
Mathlib. The certificate shapes, the checkers, the Mathlib-free soundness
statements and the producers are in the computational SPEC and are not
restated here.

This library owns no runtime search, conformance driver or compiled
benchmark. Its proof-side surface, the `rank` tactic, is measured by the
fresh-module probes under `bench/HexRankMathlib/ProofProbe` against the
unmodified pinned `eval_rank` ([The `rank` tactic](#the-rank-tactic)).
Build-only examples live in `HexRankMathlib/Tests.lean`.

Computational conformance owner: `HexRank`.

Computational performance owner: `HexRank` for the producer; this library
for the tactic.

Throughout, `e` is `HexMatrixMathlib.matrixEquiv`, `A : Hex.Matrix R n m`,
`c : Hex.Matrix.RankCert R n m`, and `B`, `C`, `P`, `U`, `d`, `r` are as
in [hex-rank §The certificate](../../HexRank/SPEC/hex-rank.md#the-certificate).

## Transport

Over `[CommRing R]`, entrywise lemmas in the style of
`HexMatrixMathlib.matrixEquiv_mul`:

```lean
theorem matrixEquiv_selectRows (A : Hex.Matrix R n m) (rows : Vector (Fin n) k) :
    e (Hex.Matrix.selectRows A rows) = (e A).submatrix rows.get id
theorem matrixEquiv_selectCols (A : Hex.Matrix R n m) (cols : Vector (Fin m) k) :
    e (Hex.Matrix.selectCols A cols) = (e A).submatrix id cols.get
theorem matrixEquiv_selectedSubmatrix (A : Hex.Matrix R n m)
    (rows : Vector (Fin n) k) (cols : Vector (Fin m) k) :
    e (Hex.Matrix.selectedSubmatrix A rows cols) = (e A).submatrix rows.get cols.get
```

together with the existing `matrixEquiv_smul` and `matrixEquiv_one` in
`HexMatrixMathlib/Algebra.lean`. The two selection lemmas belong in
`HexMatrixMathlib` (released, regenerated from this monorepo) beside
`matrixEquiv_mul`. `matrixEquiv_selectedSubmatrix` cannot, because
`selectedSubmatrix` is defined in `HexDeterminant/Minor.lean`, above
`HexMatrix`; it belongs in `HexDeterminantMathlib`, is also specified by
[hex-determinantal-ideal-mathlib](../../SPEC/Libraries/hex-determinantal-ideal-mathlib.md),
and whichever of the two planned companions lands first adds it there.

With these, `checkRank A c = true` transports to three facts about
`M := e A : Matrix (Fin n) (Fin m) R`:

```text
d ≠ 0
(M.submatrix c.rows.get c.cols.get) * e c.adj = d • 1
d • M = (M.submatrix id c.cols.get) * (e c.adj * M.submatrix c.rows.get id)
```

## Soundness for `Matrix.rank`

Over `[CommRing R] [IsDomain R] [DecidableEq R]`:

```lean
theorem checkRank_sound (h : Hex.Matrix.checkRank A c = true) :
    (e A).rank = c.rank
```

Proof, from the pinned Mathlib's `Mathlib/LinearAlgebra/Matrix/Rank.lean`:

- **Lower bound.** From the second transported identity,
  `Matrix.det_mul` and `Matrix.det_smul` with `Matrix.det_one` give
  `det B · det (e c.adj) = d ^ r`, and `pow_ne_zero` in a domain gives
  `det B ≠ 0`. `Matrix.rank_of_det_ne_zero` gives `B.rank = r`, and
  `Matrix.rank_submatrix_le` gives `r = B.rank ≤ (e A).rank`.
- **Upper bound.** `d ∈ nonZeroDivisors R` by
  `mem_nonZeroDivisors_of_ne_zero`, so
  `Matrix.rank_smul_of_mem_nonZeroDivisors` gives `(d • M).rank = M.rank`.
  The third identity and `Matrix.rank_mul_le_left` give
  `(d • M).rank ≤ (M.submatrix id c.cols.get).rank`, and
  `Matrix.rank_le_card_width` bounds that by `Fintype.card (Fin r) = r`.
  The strong rank condition these lemmas assume is
  `commRing_strongRankCondition`
  (`Mathlib/LinearAlgebra/FreeModule/StrongRankCondition.lean`) from
  `IsDomain.toNontrivial`.

The boundary cases need no separate treatment. At `r = 0` the lower bound
is `0 ≤ rank` and the upper bound is `Matrix.rank_le_card_width` at width
`0`. At `n = 0` or `m = 0` both `Matrix.rank` and `c.rank` are `0`.

The same argument goes through any injective ring homomorphism into a
domain, and that form is the one consumers use:

```lean
theorem checkRank_sound_map [CommRing R] [CommRing S] [IsDomain S] [DecidableEq R]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (h : Hex.Matrix.checkRank A c = true) :
    ((e A).map φ).rank = c.rank
```

`φ.mapMatrix` preserves products and scalar multiplication, so the three
identities hold for `(e A).map φ` with `φ d ≠ 0` by injectivity, and the
two bounds above apply over `S`. `checkRank_sound` is the case
`φ = RingHom.id R`. Note the shape `(e A).map φ` rather than
`e (A.map φ)`: `HexMatrix` has no entrywise map today, and a consumer
holding a Mathlib matrix rewrites once.

## Scalar extension

```lean
theorem rank_map_eq [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (M : Matrix (Fin n) (Fin m) R) :
    (M.map (algebraMap R K)).rank = M.rank
```

This is the one reusable scalar-extension theorem, parameterised by
`IsFractionRing R K` (`Mathlib/RingTheory/Localization/FractionRing.lean`,
an abbreviation for `IsLocalization (nonZeroDivisors R) K`), so that a
consumer is not forced through `FractionRing R`: `Rat.isFractionRing :
IsFractionRing ℤ ℚ` (same file) and the instance
`IsFractionRing K[X] (RatFunc K)` (`Mathlib/FieldTheory/RatFunc/Basic.lean`)
apply directly, and `FractionRing R` is one more instance. The pinned
Mathlib has no `Matrix.rank_map` and no statement relating `Matrix.rank`
over a domain to `Matrix.rank` over a fraction field; the closest are
`IsFractionRing.finrank_right_eq` and `IsLocalization.finrank_eq`
(`Mathlib/LinearAlgebra/Dimension/Localization.lean`), which are about a
module already over the fraction field and do not mention matrices.

Proof, through the certificate. Every domain has an exact quotient
classically: `quot a b := if h : ∃ q, a = q * b then Classical.choose h else 0`
satisfies `quot (a * b) b = a` for `b ≠ 0` by `mul_right_cancel₀`. With
`Classical.decEq R` and `IsDomain.toNontrivial`, `rankCertWith_check`
below gives a certificate `c` for `e.symm M` that checks. Then
`checkRank_sound` gives `M.rank = c.rank`, and `checkRank_sound_map` at
`φ = algebraMap R K`, injective by `IsFractionRing.injective`, gives
`(M.map φ).rank = c.rank`. The certificate is used as a proof device and
never computed.

Two consequences worth stating as corollaries:

```lean
theorem rank_map_eq_rank_fractionRing [CommRing R] [IsDomain R] (M : Matrix (Fin n) (Fin m) R) :
    (M.map (algebraMap R (FractionRing R))).rank = M.rank
theorem rank_eq_ratFunc_rank' [Field F] (M : Matrix (Fin n) (Fin m) (Polynomial F)) :
    (M.map (algebraMap (Polynomial F) (RatFunc F))).rank = M.rank
```

The second makes `HexPolySmithMathlib.rank_eq_ratFunc_rank` a statement
about `Matrix.rank` over `Polynomial F` itself, and identifies `snfRank`
with `rankWith Hex.exactDiv` over `DensePoly F` through `polyMatrixEquiv`
and `rankWith_eq` below.

A direct proof through `IsLocalizedModule` (the `K`-span of the columns of
`M.map φ` as the localisation of the `R`-span of the columns of `M`) is
possible and would not need the producer. It is not required, and the
certificate route reuses theorems this library proves anyway.

## Producer correctness

Over `[CommRing R] [DecidableEq R] [Nontrivial R]` with
`(quot : R → R → R) (hquot : ∀ a b : R, b ≠ 0 → quot (a * b) b = a)`.
`HexMatrixMathlib.isDomain_of_quot` (`HexBareissMathlib/Bareiss.lean`)
supplies the `IsDomain R` instance inside every proof.

```lean
theorem rowReduceWith_spec (A : Hex.Matrix R n m) :
    let D := Hex.Matrix.rowReduceWith quot A
    let B := (e A).submatrix D.profile.rows.get D.profile.cols.get
    D.denom = B.det ∧
    (∀ k : Fin D.profile.rank,
      (e D.matrix) (D.profile.rows.get k) = (B.adjugate * (e A).submatrix D.profile.rows.get id) k) ∧
    (∀ i, i ∉ D.profile.rows.toList → (e D.matrix) i = 0)
theorem rankCertWith_check (A : Hex.Matrix R n m) :
    Hex.Matrix.checkRank A (Hex.Matrix.rankCertWith quot A) = true
theorem rankWith_eq (A : Hex.Matrix R n m) :
    Hex.Matrix.rankWith quot A = (e A).rank
theorem rank_eq (A : Hex.Matrix Int n m) :
    Hex.Matrix.rank A = (e A).rank
theorem exists_rankCert [CommRing R] [IsDomain R] [DecidableEq R] (A : Hex.Matrix R n m) :
    ∃ c : Hex.Matrix.RankCert R n m, Hex.Matrix.checkRank A c = true
```

`exists_rankCert` is completeness with no quotient hypothesis: the
classical exact quotient of [Scalar extension](#scalar-extension) and
`rankCertWith_check` supply the witness. The adjugate argument of
[hex-rank §Completeness](../../HexRank/SPEC/hex-rank.md#completeness) is an alternative proof
that does not go through the producer.

`rowReduceWith_spec` is proved by induction along the column loop with the
invariant of
[hex-rank §Exactness and producer correctness](../../HexRank/SPEC/hex-rank.md#exactness-and-producer-correctness):
after `k` pivots with block `B_k` and `p = B_k.det`, the pivot rows of the
state are `B_k.adjugate * P_k` and each non-pivot row `i` is
`p • A[i, :] − A[i, cols] * (B_k.adjugate * P_k)`. The pivot step first
identifies the new pivot with `B_{k+1}.det` by the bordered-determinant
identity `det [[B_k, u], [vᵀ, x]] = x · det B_k − vᵀ * B_k.adjugate * u`
(Laplace expansion along the last row, `Matrix.det_succ_row` and
`Matrix.adjugate_apply`), so that `B_{k+1}` is nonsingular, and then
verifies the update against the invariant by left-multiplying by
`B_{k+1}` and cancelling the nonzero scalar `B_{k+1}.det` in a domain,
using `Matrix.mul_adjugate` (`Mathlib/LinearAlgebra/Matrix/Adjugate.lean`).
Those are the only determinant facts used. That equality is what turns each
`quot (…) prev` into the primed invariant value through `hquot`, so
exactness of every division is a consequence of the invariant and not a
separate hypothesis. The skip step changes nothing. `denom = B.det` is the
invariant's `prev = p` at the end. No Desnanot-Jacobi or Sylvester
identity is used, and `HexMatrixMathlib.desnanot_jacobi_borderedMinor` is
not imported for this proof.

`rankCertWith_check` applies `rowReduceWith_spec` to the pass over `A`
(for `rows`, `cols`) and to the pass over `[B | 1]` (for `adj` and
`denom`): the second pass has every column a pivot column and every row a
pivot row in some order `π`, its reported pivot rows restricted to the
right block are `(B.submatrix π id).adjugate * (1 : Matrix).submatrix π id`,
which is `sign π • B.adjugate` by `Matrix.adjugate_mul_distrib` and the
adjugate of a permutation matrix, and its `denom` is
`(B.submatrix π id).det = sign π • B.det`. The three identities then hold
with the common sign. Identity 3 for a non-pivot row is the "non-pivot
rows are zero" clause of the first pass, read as
`p • A[i, :] = A[i, cols] * (B.adjugate * P)`.

`rankWith_eq` is `rankCertWith_check` composed with `checkRank_sound`, and
`rank_eq` is its instance at `quot := HexArith.Int.exactDiv`,
`hquot := Int.mul_ediv_cancel`.

### The rank profile

Over `[CommRing R] [IsDomain R]`, for `M : Matrix (Fin n) (Fin m) R`, define
the two profiles as predicates on index lists:

```lean
def IsColRankProfile (M : Matrix (Fin n) (Fin m) R) (J : List (Fin m)) : Prop :=
  ∀ j, j ∈ J ↔ (M.submatrix id (Fin.castLE (Nat.succ_le_of_lt j.isLt))).rank
                = (M.submatrix id (Fin.castLE j.isLt.le)).rank + 1
def IsRowRankProfile (M : Matrix (Fin n) (Fin m) R) (I : List (Fin n)) : Prop :=
  ∀ i, i ∈ I ↔ (M.submatrix (Fin.castLE (Nat.succ_le_of_lt i.isLt)) id).rank
                = (M.submatrix (Fin.castLE i.isLt.le) id).rank + 1

theorem rowReduceWith_cols_eq_colProfile (A : Hex.Matrix R n m) :
    IsColRankProfile (e A) (Hex.Matrix.rowReduceWith quot A).profile.cols.toList
theorem rowReduceWith_rows_eq_rowProfile (A : Hex.Matrix R n m) :
    IsRowRankProfile (e A) (Hex.Matrix.rowReduceWith quot A).profile.rows.toList
```

(`Fin.castLE` embeds the first `j` or `j + 1` indices.) Both are proved
from `rowReduceWith_spec` and `checkRank_sound`: column `j` is a pivot
column exactly when the reduced form has a nonzero entry in column `j` in
some non-pivot row at the moment column `j` is scanned, and that is
exactly when the rank of the first `j + 1` columns exceeds the rank of the
first `j`. The row statement is the argument in
[hex-rank §The rank profile](../../HexRank/SPEC/hex-rank.md#the-rank-profile), formalised as:
the chosen pivot row at each step is the least-index non-pivot row with a
nonzero eliminated entry, and every smaller-index non-pivot row with a
nonzero eliminated entry would have been chosen first, so the chosen row
is not in the span of the rows before it. Neither theorem is needed for
`rank_eq`; they are what makes `rankProfileWith` an API rather than an
implementation detail.

## Relation to `Echelon.Decomposition`

The pinned Mathlib's certificate
(`Mathlib/LinearAlgebra/Matrix/Echelon/Decomposition.lean`, namespace
`Echelon`, over `[Fintype m] [LinearOrder m] [Fintype n] [LinearOrder n]
[CommRing R] [IsDomain R]`) is

```lean
structure Decomposition (A : Matrix m n R) where
  L : Matrix m m R
  σ : Equiv.Perm m
  pivot : m → WithTop n
  isPivotedBy : (L * (A.submatrix σ id)).IsPivotedBy pivot
  L_lowerTriangular : L.IsLowerTriangular
  L_diag_ne_zero (i : m) : L.diag i ≠ 0
```

with `Decomposition.rank_eq : A.rank = #{i | cert.pivot i ≠ ⊤}`. Its
checker is the `Decidable (A.IsPivotedBy l)` instance of
`Mathlib/LinearAlgebra/Matrix/Echelon/Pivot.lean`, run by `decide` in the
kernel on the product `L * A.submatrix σ id` (`certifyCondition` in
`Mathlib/Tactic/Echelon/Bareiss.lean`). It carries an `n × n`
transform and no minor; the Hex certificate carries an `r × r` adjugate
and no transform. Neither is a projection of the other, and the two
conversions below each compute one `r × r` object.

**From a Hex certificate.** A checked certificate alone does not
determine a `Decomposition`, because `checkRank` accepts index sets that
no echelon form has: on `A = [[1, 1]]` the certificate
`rows = [0], cols = [1], denom = 1, adj = [[1]]` checks, but no echelon
form of `A` has its pivot in column `1`; and on `B = [[0, 1], [1, 0]]`
(the canonical certificate of that matrix) no lower triangular `T` with
nonzero diagonal makes `T * B` upper triangular with nonzero diagonal,
since the `(1, 0)` entry of `T * B` is the `(1, 1)` entry of `T`. The
adapter therefore takes, besides the certificate, a lower triangular
transform `T` of the pivot block together with the echelon condition it
has to produce:

```lean
def RankCert.toDecomposition (h : Hex.Matrix.checkRank A c = true)
    (T : Matrix (Fin c.rank) (Fin c.rank) R) (hT : T.IsLowerTriangular)
    (hTd : ∀ i, T.diag i ≠ 0)
    (hTP : (T * (e A).submatrix c.rows.get id).IsPivotedBy (fun k => ↑(c.cols.get k))) :
    Echelon.Decomposition (e A)
theorem RankCert.toDecomposition_pivot_card (h T hT hTd hTP) :
    #{i | (RankCert.toDecomposition h T hT hTd hTP).pivot i ≠ ⊤} = c.rank
```

with

```text
σ     := the permutation moving c.rows to positions 0 … r - 1 in order
L     := [[T, 0], [-(M.submatrix id c.cols.get restricted to non-pivot rows) * e c.adj, d • 1]]
pivot := fun i => if i < r then ↑(c.cols.get i) else ⊤
```

`L` is block lower triangular with triangular diagonal blocks and diagonal
entries the diagonal of `T` and `d`, all nonzero. The first `r` rows of
`L * M.submatrix σ id` are `T * (M.submatrix c.rows.get id)`, pivoted at
`c.cols` by `hTP` (which forces `c.cols` strictly increasing). The
remaining rows are `d • M[i, :] − M[i, cols] * (e c.adj * P)`, which is
`0` by identity 3. Existence is then a statement about the producer's
certificates, not about arbitrary checked ones:

```lean
theorem nonempty_decomposition [CommRing R] [IsDomain R] (A : Hex.Matrix R n m) :
    Nonempty (Echelon.Decomposition (e A))
theorem exists_decomposition_of_checkRank (h : Hex.Matrix.checkRank A c = true) :
    ∃ D : Echelon.Decomposition (e A), #{i | D.pivot i ≠ ⊤} = c.rank
```

The first is proved on `rankCertWith quot A` for the classical quotient:
its `rows` are in elimination order and its `cols` strictly increasing,
every leading principal minor of its `B` is a pivot of the run and so
nonzero, and the below-only fraction-free elimination of `B` in that
order (Bareiss 1968) supplies `T` over `R` with `T * P` in echelon form
at `cols`, the columns between pivot columns being zero in every
non-pivot row at the moment they were skipped. The second is the first
together with `Decomposition.rank_eq` and `checkRank_sound`, and does
not go through the given certificate's index sets.

`T` is an input because this library does not compute it: it is the
transform of a below-only fraction-free pass over `B`, which
`Hex.Matrix.bareissNoPivotWith` performs without reporting. The
executable adapter that produces `T`, and the `bareiss_ext` model that
lets Hex's producer feed `norm_rank` directly, are hex-matrix-tactic's
(https://github.com/kim-em/hex-dev/issues/10151), which names both.

**From a Decomposition.** Given `D : Echelon.Decomposition (e A)` with
`r := #{i | D.pivot i ≠ ⊤}`, the rows with a pivot are the first `r` rows
of `L * M.submatrix σ id` (`IsPivotedBy.monotone`), so
`rows := (D.σ 0, …, D.σ (r - 1))` and `cols :=` the pivot columns in
order. The `r × r` block of `M.submatrix σ id` at those positions is
`(L.submatrix (first r) (first r))⁻¹ * (echelon block)` over the fraction
field, a product of a lower triangular and an upper triangular matrix
with nonzero diagonals, so its determinant is nonzero. Then
`d := B.det`, `adj := B.adjugate`, and the three identities hold by
`Matrix.mul_adjugate` and the argument of
[hex-rank §Completeness](../../HexRank/SPEC/hex-rank.md#completeness):

```lean
theorem exists_rankCert_of_decomposition (D : Echelon.Decomposition (e A)) :
    ∃ c : Hex.Matrix.RankCert R n m,
      Hex.Matrix.checkRank A c = true ∧ c.rank = #{i | D.pivot i ≠ ⊤}
```

The executable form runs `rankCertWith`'s second pass on `[B | 1]` for
`adj` and `denom`, with `rows`, `cols` read off `D`; it is one `O(r³)`
pass and no elimination of `A`.

## Kernel certificate

`HexRankMathlib/Kernel.lean` proves the kernel certificate of
[hex-rank §The kernel certificate](../../HexRank/SPEC/hex-rank.md#the-kernel-certificate) sound
for `Matrix.rank` over `ℤ`, stated on the Mathlib matrix directly:

```lean
def vecOfList [Zero α] : (k : Nat) → List α → (Fin k → α)
def ofLists [Zero α] (n m : Nat) (L : List (List α)) : Matrix (Fin n) (Fin m) α
theorem ofLists_apply (L) (i : Fin n) (j : Fin m) : ofLists n m L i j = (L.getD i []).getD j 0
theorem rank_eq_of_checkList (n m) (L) (c : RankWitness)
    (h : checkRankList n m L c = true) : (ofLists n m L).rank = c.rank
theorem rank_eq_of_checkList' (A : Matrix (Fin n) (Fin m) ℤ) (L) (c)
    (hA : A = ofLists n m L) (h : checkRankList n m L c = true) : A.rank = c.rank
theorem rank_le_of_checkList' … (hr : c.rank ≤ r) : A.rank ≤ r
theorem le_rank_of_checkList' … (hr : r ≤ c.rank) : r ≤ A.rank
```

`vecOfList (k + 1) (a :: l)` unfolds to `vecCons a (vecOfList k l)`, so a
literal `!![…]` is *definitionally* `ofLists n m [[…], …]` of its own
entry expressions, one unfolding per entry; `hA` is `rfl`, and the kernel
never evaluates an entry through `Matrix.of` and `vecCons` inside the
arithmetic. This matters: reading the entries of a `16 × 16` literal by
kernel evaluation of `A i j` costs about `200 ms`, more than the whole
certificate check, while the definitional identification costs `6 ms`.

The proof follows `rank_eq_of_cert`. Lower bound: with `B` the pivot block
`A.submatrix rows cols` and `V̄` the matrix of `vt` over `ZMod modulus`
(zero below the diagonal), the product `B.map Int.cast * V̄` is lower
triangular with unit diagonal (`Matrix.IsLowerTriangular`,
`det_of_isLowerTriangular`), so its determinant is `1`, `det B` is nonzero
in `ZMod modulus` (`Int.cast_det`, nontrivial since `modulus ≥ 2`) and so
in `ℤ`; then `rank_of_det_ne_zero` and `rank_submatrix_le`. Upper bound:
for every row `i` there are coefficients `w` with `denom * A i j =
Σ_l w l * A (rows l) j`, from the pivot rows themselves or from the
consumed `z` row, so `denom • A = W * A.submatrix rows id` for `W` built
from the chosen coefficients (`Classical.choose`, no injectivity of
`rows` needed), and `rank_smul_of_mem_nonZeroDivisors`, `rank_mul_le_right`,
`rank_le_card_height`. The bridge from lists to sums is
`dotNat_eq_sum`, `combo_getD` and `rowsCheck_spec`, each by induction on
the list the checker recurses on.

## The `rank` tactic

`HexRankMathlib/Tactic.lean` declares the non-reserved tactic keyword
`rank`, closing

```text
A.rank = r      r = A.rank
A.rank ≤ r      r ≥ A.rank
r ≤ A.rank      A.rank ≥ r
```

for `A : Matrix (Fin n) (Fin m) ℤ` a closed `!![…]` or `Matrix.of ![…]`
literal, possibly behind definitions (unfolded within a small budget), and
`r` a closed natural number. Entries are closed integer expressions that
`norm_num` evaluates (`1 - 1` is accepted; the kernel then reduces
`1 - 1` itself when the checker reads it).

The tactic evaluates the entries with Mathlib's `evalRatEntry`, runs the
compiled `Hex.Matrix.rankWitness`, quotes the witness with `toExpr`, and
builds `rank_eq_of_checkList' A L c rfl (of_decide_eq_true rfl)` composed
with a kernel-decided comparison of `c.rank` with `r`; the whole proof is
added as an auxiliary theorem (`mkAuxTheorem`) so the kernel checks it
exactly once. Outcomes follow the matrix-tactic protocol: a goal that is
not a rank comparison is not applicable; a matrix with free variables, a
non-integer carrier or a non-literal closed matrix is declined with the
reason; a false target is reported with the certified rank before any
proof is built; a certificate the kernel rejects is a failure, diagnosed
by evaluating each decided proposition. Accepted theorems depend on
`propext`, `Classical.choice` and `Quot.sound` only.

**Comparator.** The unmodified pinned `eval_rank` is the comparator. The
fresh-module probes `bench/HexRankMathlib/ProofProbe/{Dense8,Dense16,
Deficient16,Dense32,LowRank32}{Hex,Mathlib}.lean` prove the same literal
by `rank` and by `eval_rank`, each against its import-only baseline
(`Baseline`, `MathlibBaseline`); `scripts/bench/rank_tactic_sweep.py`
runs them through `fresh_module_sweep.py` (six samples, adjacent pairs,
alternating orientation) and the family's comparator ratio is the
`eval_rank` delta over the `rank` delta. Kernel-only times on the same
literals, one run each on the shared host (`lake lean -Dprofiler=true`):

| family | `eval_rank` | `rank` |
|---|---|---|
| dense `8 × 8`, rank 8 | 121 ms | 19 ms |
| dense `16 × 16`, rank 16 | 864 ms | 115 ms |
| dense `16 × 16`, rank 14 | 851 ms | 117 ms |
| dense `32 × 32`, rank 32 | 6.8 s | 1.1 s |
| `32 × 32`, rank 2 | 7.3 s | 116 ms |

Rationals are a follow-up: clear each row's denominators (the rank is
unchanged), certify the integer matrix, and check the scaling in the
kernel. Rank goals on `Hex.Matrix` inputs are hex-matrix-tactic's; the
witness cannot certify the executable's own value without a Mathlib-free
rank theory.

## Decidability

```lean
instance (A : Matrix (Fin n) (Fin m) ℤ) (r : Nat) : Decidable (A.rank = r)
```

by `rank_eq` at `e.symm A`, in the style of hex-berlekamp-mathlib's
`Decidable (Irreducible f)`. This is the instance
[hex-modular-matrix](../../SPEC/Libraries/hex-modular-matrix.md) planned for its `rank`, now
supplied here with the direct algorithm; the multi-modular route may
later replace the computation behind it without changing the statement.
A generic instance for every carrier with an executable exact quotient is
not declared, because the quotient is a function argument and not an
instance; a carrier consumer writes the one-line
`decidable_of_iff (rankWith quot A = r)` with `rankWith_eq`.

## Mathlib inventory

Checked against the pinned Mathlib, `v4.34.0-rc2` (Mathlib commit
`85e3a25e006c35636f0e53b0e9296caca2685bc0`), by file path:

- `Mathlib/LinearAlgebra/Matrix/Echelon/Decomposition.lean`:
  `Echelon.Decomposition` and `Echelon.Decomposition.rank_eq`, the only
  declarations in the file, over `[CommRing R] [IsDomain R]`.
- `Mathlib/LinearAlgebra/Matrix/Echelon/Pivot.lean`: `Matrix.IsPivotedBy`,
  `Matrix.IsPivotedBy.rank_eq`, `Matrix.IsPivotedBy.monotone`, and the
  `Decidable (A.IsPivotedBy l)` instance.
- `Mathlib/Tactic/NormRank.lean` and `Mathlib/Tactic/Echelon/{Core,Bareiss,Rat,Zsqrtd,Parsing}.lean`:
  `norm_rank`, `eval_rank`, `certifyCondition`, `bareissDecomp`,
  `BareissExt`, `bareiss_ext`. The elimination invariant there is not a
  theorem; only the final certificate is kernel-checked.
- `Mathlib/LinearAlgebra/Matrix/Rank.lean`: `Matrix.rank`,
  `rank_of_det_ne_zero`, `rank_submatrix_le`, `rank_mul_le_left`,
  `rank_le_card_width`, `rank_smul_of_mem_nonZeroDivisors`,
  `rank_mul_eq_left_of_det_ne_zero`, `rank_mul_eq_right_of_det_ne_zero`.
- `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`: `det_mul`,
  `det_smul`, `det_one`, `RingHom.map_det`.
- `Mathlib/LinearAlgebra/Matrix/Adjugate.lean`: `adjugate`,
  `mul_adjugate`, `adjugate_mul`, `adjugate_mul_distrib`.
- `Mathlib/RingTheory/Localization/FractionRing.lean`: `IsFractionRing`
  (an `abbrev` for `IsLocalization (nonZeroDivisors R) K`),
  `IsFractionRing.injective`, `IsFractionRing.to_map_eq_zero_iff`,
  `Rat.isFractionRing`, `FractionRing`.
- `Mathlib/FieldTheory/RatFunc/Basic.lean`: the instance
  `IsFractionRing K[X] (RatFunc K)`.
- `Mathlib/LinearAlgebra/Dimension/Localization.lean`:
  `IsLocalization.finrank_eq`, `IsFractionRing.finrank_right_eq`, about
  modules over the fraction field, not matrices.
- **Absent.** `Matrix.rank_map`, any lemma relating `Matrix.rank A` to
  `Matrix.rank (A.map (algebraMap R K))`, any "rank equals the largest
  nonzero minor" lemma, any rank lemma parameterised over a `RingHom`,
  and any statement about the generic rank of a polynomial matrix.
  `rank_map_eq` and `checkRank_sound_map` are therefore new, and if
  Mathlib gains either, this library should state agreement with it
  rather than a second copy.

An implementer must re-run these searches when the Mathlib pin moves.

## Tests

`HexRankMathlib/Tests.lean`, build-only:

- `checkRank_sound` on a closed `Hex.Matrix ℤ 3 4` of rank `2` with a
  hand-written certificate, the check discharged by `decide +kernel`,
  concluding `(e A).rank = 2`;
- `rank_eq` on the same matrix through `Hex.Matrix.rank`, and the
  `Decidable (A.rank = r)` instance on its Mathlib form by `decide`;
- `rank_map_eq` instantiated at `IsFractionRing ℤ ℚ` and at
  `IsFractionRing ℚ[X] (RatFunc ℚ)`, to check the instances resolve
  without going through `FractionRing`;
- `exists_decomposition_of_checkRank` and
  `exists_rankCert_of_decomposition` on a `2 × 2` matrix of rank `1`, to
  check that the hypotheses are stated in the form a consumer has;
- the `rank` tactic in every orientation on the `3 × 4` example, on
  `!![…]` with a compound entry, on `Matrix.of ![…]`, on the empty shapes,
  on a `16 × 16` full-rank and a `32 × 32` rank-`2` literal, and its
  messages on a false target, a symbolic matrix, a rational matrix and a
  closed non-literal (`#guard_msgs`).

These are not an independent oracle. The conformance stream of `HexRank`
is.
