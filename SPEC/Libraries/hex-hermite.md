# hex-hermite (Hermite normal form over `Int`, depends on hex-row-reduce, hex-arith, hex-bareiss)

The Hermite normal form of an integer matrix: a canonical row-echelon
representative of the integer row lattice, together with the unimodular
transform that produces it and the transform's inverse. Mathlib-free;
the companion `hex-hermite-mathlib` relates the executable output to
`Submodule.span ℤ`, `Matrix.rank`, and the general linear group over `ℤ`.

This SPEC and [hex-smith](hex-smith.md) are a pair. Hermite normal form
uses row operations alone and is the ℤ analogue of reduced row echelon
form. Smith normal form uses row and column operations, is diagonal, and
is built on top of this library. Material shared by the two (the
unimodular certificate shape, entry growth, the oracle) is specified
here and referenced there.

## Why this library exists

Row reduction in `hex-row-reduce` requires a field: `rowReduce`,
`spanCoeffs`, and `nullspace` all carry `[Lean.Grind.Field R]`, because
the pivot step divides. Over `Int` the corresponding statements are
about the row *lattice* rather than the row *space*, and they are
strictly finer: `[[2, 0], [0, 2]]` and `[[1, 0], [0, 1]]` span the same
subspace of `ℚ²` and different sublattices of `ℤ²`. Hermite normal form
is the object that decides lattice questions the way reduced row echelon
form decides subspace questions.

What the library delivers, none of which is currently reachable:

- **A canonical form for an integer row lattice.** Two matrices *of the
  same dimensions* have the same integer row lattice exactly when their
  Hermite normal forms are equal, so lattice equality is decided by one
  comparison. Across dimensions the comparison is on `hnfBasis`, the
  nonzero rows alone. See "Canonicity is per shape" below.
- **Lattice membership with completeness.** `latticeContains A v` is
  `true` exactly when `v` is an integer combination of the rows of `A`.
  The `Field`-based `spanContains` answers the rational question and
  says nothing about the integer one.
- **An integer kernel basis.** The rows of the transform that map to
  zero generate the whole kernel lattice `{x | vecMul x A = 0}`, not a
  finite-index sublattice of it. Saturation is what makes this
  different from clearing denominators in the rational nullspace.
- **Integer rank** as the count of nonzero rows, computed without
  passing through `ℚ`.
- **The index of a finite-index sublattice**, as the product of the
  pivots. Finite index means rank equal to the number of *columns*, so
  this covers a tall matrix with `m` independent rows and never a wide
  one.

Named consumers:

- **hex-smith**, which computes its diagonalisation from this library's
  elimination step and reuses its certificate shape.
- **hex-number-field** and the maximal-order work in
  [future-work](../future-work.md), where module and ideal bases over
  `ℤ` are stored in Hermite normal form and index computations are
  exactly the pivot product above.
- **hex-lll**, which can canonicalise a reduced basis and drop
  dependent generators. The dependency runs from this library to
  `hex-lll`'s vocabulary rather than the other way. See "Prerequisite
  changes in other libraries".
- The **polynomial-matrix invariant factors** item in
  [future-work](../future-work.md), which needs the same algorithm shape
  over `F[x]`. That is not this library. See "Why `Int` and not a
  Euclidean domain class".

## The convention this library fixes

`A : Matrix Int n m`. A **Hermite normal form** of `A` is a pair
`(U, H)` with `U : Matrix Int n n` unimodular (invertible over `ℤ`) and
`H = U * A` satisfying:

1. `H` has `r` nonzero rows, in rows `0 … r-1`, and rows `r … n-1` are
   zero.
2. Row `i < r` has its leading nonzero entry in column `jᵢ`, and
   `j₀ < j₁ < ⋯ < j_{r-1}`.
3. Each pivot `H[i][jᵢ]` is positive.
4. Every entry above a pivot is reduced into the pivot's residue range:
   `0 ≤ H[k][jᵢ] < H[i][jᵢ]` for `k < i`.

This is the row-style form: `U` multiplies on the left, pivots move
right as the row index increases, and the reduction is applied to the
entries *above* each pivot. It matches the shape `RowEchelonData` and
`IsEchelonForm` already describe, which is why the hex-row-reduce SPEC
calls `IsEchelonForm` the "shared conditions for any echelon form (RREF
or HNF)".

**`H` is unique; `U` is not.** Uniqueness of `H` is the property the
whole library rests on: its nonzero rows depend only on the integer row
lattice of `A`. `U` is determined only when `A` has full row rank. When
`rank < n` the rows of `U` that map to zero can be changed by any
unimodular transformation of the kernel lattice. No uniqueness theorem
for `U` is stated or should be expected.

**Canonicity is per shape.** `hnf A : Matrix Int n m` keeps the `n - r`
zero rows, so it is canonical among `n × m` matrices and not across
presentations of the same lattice. `[1]` and `[[1], [0]]` generate the
same lattice in `ℤ¹` and their Hermite normal forms do not even have the
same type. The presentation-independent object is therefore

```lean
/-- The nonzero rows of `hnf A`: a canonical basis of the row lattice,
independent of how many generators were supplied. -/
def hnfBasis (A : Matrix Int n m) : Matrix Int (hnfRank A) m
```

and it is `hnfBasis` that the cross-presentation statements, the
"drop dependent generators" consumer, and the conformance case comparing
two presentations of one lattice all use. Every claim about `hnf` itself
is qualified by "among matrices of the same dimensions".

**Other systems use other conventions**, and the differences are exactly
the four clauses above: column-style versus row-style, reduction above
versus below the pivot, zero rows first versus last, and pivot sign.
FLINT's `fmpz_mat_hnf` is row-style with reduction above the pivot,
matching this SPEC. PARI's `mathnf` is column-style and returns its zero
columns first. Normalising between conventions is the oracle driver's
job, and is called out again under "Conformance", because a convention
mismatch produces a plausible-looking matrix that fails equality on
every input and is easy to misread as an algorithm bug.

## The echelon contract is weaker than it looks

`IsEchelonForm` and `IsRowReduced` (`HexRowReduce/RowEchelon/Contracts.lean`)
do **not** require the declared pivot to be the leading nonzero entry of
its row. Nothing in `pivotCols_sorted`, `below_pivot_zero`, or
`zero_row` constrains an entry that lies to the left of a pivot in a
non-pivot column. The following elaborates against the current tree:

```lean
/-- The 1x2 matrix `[[5, 1]]`. -/
@[expose] def cexM : Matrix Int 1 2 := ⟨#v[5, 1]⟩

/-- Declares rank `1` with pivot column `1`, and the identity transform. -/
@[expose] def cexD : RowEchelonData Int 1 2 :=
  { rank := 1, echelon := cexM, transform := Matrix.identity 1,
    pivotCols := #v[(1 : Fin 2)] }

example : IsRowReduced cexM cexD where
  transform_mul := by simp [cexD]
  transform_inv := ⟨Matrix.identity 1, by simp [cexD]⟩
  transform_right_inv := ⟨Matrix.identity 1, by simp [cexD]⟩
  rank_le_n := by simp [cexD]
  rank_le_m := by simp [cexD]
  pivotCols_sorted := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    have hj' : j < 1 := hj
    simp [Fin.lt_def] at h
    omega
  below_pivot_zero := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    have hj' : j < 1 := hj
    simp at h
    omega
  zero_row := by
    rintro ⟨j, hj⟩ h
    have hj' : j < 1 := hj
    simp [cexD] at h
    omega
  pivot_one := by
    rintro ⟨i, hi⟩
    have hi' : i < 1 := hi
    obtain rfl : i = 0 := by omega
    simp [cexD, cexM, getRow, Vector.get]
  above_pivot_zero := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ h
    have hi' : i < 1 := hi
    have hj' : j < 1 := hj
    simp at h
    omega
```

Every field is vacuous or immediate, yet `5` sits to the left of the
declared pivot, so this is not a row echelon form under any standard
definition. `rowReduce` of course produces leading pivots. The point is
that the *contract* does not say so, and a downstream proof may not
assume it.

Two consequences for this SPEC.

**`IsHNF` must state the leading-entry condition itself.** Without it
uniqueness is false: `[[5, 1]]` and `[[0, 1]]` would both be Hermite
normal forms of `[[5, 1]]` with pivot column `1`, and they are different
matrices. The condition is clause 2 above, and it appears as
`pivot_leading` below.

**The clause list in [future-work](../future-work.md) is wrong in both
directions.** It proposes three HNF-specific fields, of which
`det transform = 1 ∨ det transform = -1` is redundant, and it omits the
leading-entry condition, which is required. Redundant because
`IsEchelonForm.transform_inv` already supplies an integer matrix `Tinv`
with `Tinv * transform = 1`, and `det_mul` (Mathlib-free, in
`HexDeterminant/Adjugate.lean`) turns that into
`det Tinv * det transform = 1`, hence `det transform = ±1`. So it is a
theorem about `IsEchelonForm` over `Int`, stated once, not a field every
construction has to discharge.

## The contract

```lean
/-- Hermite normal form conditions on top of `IsEchelonForm`, over `Int`. -/
structure IsHNF {n m : Nat} (M : Matrix Int n m) (D : RowEchelonData Int n m) : Prop
    extends IsEchelonForm M D where
  pivot_leading : ∀ (i : Fin D.rank) (j : Fin m),
      j < D.pivotCols.get i → D.echelon[i][j] = 0
  pivot_pos : ∀ (i : Fin D.rank), 0 < D.echelon[i][D.pivotCols.get i]
  above_nonneg : ∀ (i : Fin D.rank) (k : Fin n), k.val < i.val →
      0 ≤ D.echelon[k][D.pivotCols.get i]
  above_lt : ∀ (i : Fin D.rank) (k : Fin n), k.val < i.val →
      D.echelon[k][D.pivotCols.get i] < D.echelon[i][D.pivotCols.get i]
```

This elaborates as written against the current tree. `above_nonneg` and
`above_lt` are separate fields rather than one conjunction so that each
can be cited on its own. Together they are the "reduced into
`[0, pivot)`" condition. The `D.echelon[i]` access with `i : Fin D.rank` is the same
shape `IsRowReduced.pivot_one` already uses.

The unimodularity of `D.transform` is inherited from
`IsEchelonForm.transform_inv` and `transform_right_inv`, and is restated
as a theorem:

```lean
theorem IsHNF.det_transform (h : IsHNF M D) :
    det D.transform = 1 ∨ det D.transform = -1
```

## The elimination step

Two entries `a` and `b` in the same column, with `(g, s, t) :=
HexArith.Int.extGcd a b` so that `g = Int.gcd a b` and `s * a + t * b = g`.
The 2x2 integer matrix

```
E = ⎡    s      t  ⎤          E⁻¹ = ⎡ a/g   -t ⎤
    ⎣ -b/g   a/g  ⎦                ⎣ b/g    s ⎦
```

applied to the two rows replaces `(a, b)` by `(g, 0)`. Both divisions
are exact (`g` divides `a` and `b`), and they follow the two-layer design
`hex-bareiss` uses rather than putting a proof-carrying division on the
value path: the executable loop calls a proof-free `exactDiv num denom :=
num / denom` with an `@[extern]` binding, and a separate theorem
`exactDiv_eq_divExact` identifies it with `Int.divExact` wherever
divisibility is known (`HexBareiss/Bareiss.lean`). Since that primitive
is now wanted by two libraries, it should move to `hex-arith` next to
`extGcd` rather than be copied. `det E =
(s * a + t * b) / g = 1`, and the displayed `E⁻¹` is its inverse by
direct computation, so *the inverse transform is available at every step
without a determinant or an adjugate*. Accumulating `U` and `W` together
costs one extra row update per step and makes
`IsEchelonForm.transform_inv` data rather than an existence proof to be
recovered later.

`extGcd` returns `g : Nat`, so `g` is nonnegative by construction and
the pivot-positivity clause needs no separate sign fixup except when the
whole column is zero, where the step is skipped.

Reduction above a pivot `p > 0`: for each row `k < i`, subtract
`(H[k][jᵢ] / p)` times row `i`. Lean's `Int` division and modulus are
Euclidean (`(-7) / 3 = -3` and `(-7) % 3 = 2`), so the resulting entry
is exactly `H[k][jᵢ] % p`, which lies in `[0, p)` by `Int.emod_nonneg`
and the corresponding upper bound. No sign analysis is needed, and the
`above_nonneg` and `above_lt` fields follow from the two standard
`Int.emod` lemmas.

## Entry growth is the design problem

The elimination above is correct and unusable on its own. Intermediate
entries of naive integer elimination grow far beyond the size of the
answer: the output is bounded (for square nonsingular `A`, every entry
of `H` is at most `|det A|`, and the pivot product is exactly `|det A|`)
while the intermediate matrices are not. This is the classical
observation that makes integer elimination a different subject from
elimination over a field, and it is the same phenomenon `hex-bareiss`
addresses for determinants by exact division.

Three responses, all standard, and this SPEC takes the first two.

**The default is total, and is the one the public `hnf` runs.** Process
the columns left to right, and after each new pivot is fixed, reduce
every entry above it immediately rather than at the end. Reducing eagerly
is what keeps the already-processed part of the matrix bounded by its own
pivots instead of letting it accumulate across the run. The rows not yet
consumed are not bounded by anything, which is the honest statement, and
is why the input families under "Benchmarking" measure entry size and not
only time.

This is deliberately *not* called Kannan-Bachem. Kannan-Bachem maintains
Hermite normal forms of leading *nonsingular* minors and reorders rows
and columns to produce them, and its entry bound is a cofactor bound that
holds for that arrangement. Its FLINT analogue `hnf_minors` carries a
rank precondition. The public `hnf` here takes arbitrary rectangular and
rank-deficient input, where a leading minor determinant can be zero and
the bound says nothing. Specifying rank-profile preprocessing, the
full-rank subproblem it produces, and the reconstruction of the zero rows
and the transform is real work and is listed under "Open questions" as
the optimisation to measure against the total algorithm, not smuggled in
as the default.

**A modular variant for square nonsingular input.** For square
nonsingular `A` with `d = |det A|`, the row lattice `L` contains `d·ℤⁿ`
(because `d · A⁻¹` is `± adj A`, an integer matrix), so `L = L + d·ℤⁿ`
and the Hermite normal form of `A` is the Hermite normal form of the
`(2n) × n` matrix `[A; d·I]`. That augmented lattice is what makes
modular arithmetic legitimate, and the statement has to be made in that
form rather than as "reduce every entry modulo `d`":

> Reducing a generator modulo `d` is **not** a lattice-preserving
> operation on its own. For `A = [2]` and `d = 2`, the row `[2]` reduces
> to `[0]`, which generates the zero lattice rather than `2ℤ`.

What is legitimate is to compute in `ℤ/dℤ` while the generators of
`d·ℤⁿ` remain present, which is what the Domich-Kannan-Trotter algorithm
does: each pivot is `gcd` of the column entries *with `d`*, and a pivot
may equal `d` itself, so entries live in `[0, d]` rather than `[0, d)`.
The SPEC for `hnfSquare` is the DKT recurrence on `[A; d·I]`, not
elimination with a modulus bolted on, and the implementation must
represent the pivot value `d` rather than reducing it to `0`. `d` comes
from `hex-bareiss`, which is why this library depends on it.

**LLL-based reduction is deliberately not in v1.** The
Havas-Majewski-Matthews algorithm controls growth by LLL-reducing the
working rows, and `hex-lll` exists. It is left out until the benchmark
under "Benchmarking" shows growth rather than operation count to be the
constraint on a real input family, because the dependency is heavy
(`hex-lll` pulls in `hex-gram-schmidt`) and the payoff is
input-dependent. The threshold that would justify adding it is written
down under "Benchmarking".

**The transform costs more than the form.** `U` is larger than `H`, often
much larger, and computing it is the dominant cost on hard inputs. This
is not an artefact of a particular algorithm: `H` is bounded by the
determinant while `U ≈ H · A⁻¹` is bounded by the determinant times the
size of `A⁻¹`. FLINT's separate `fmpz_mat_hnf` and
`fmpz_mat_hnf_transform` entry points are evidence that production
implementations treat this as two operations, and this SPEC does the
same: `hnf` returns the form alone and `hnfData` returns the form with
the transform and its inverse. A caller who only wants lattice equality,
rank, or the index must not be made to pay for `U`.

## API

```lean
namespace Hex.Matrix

/-- The Hermite normal form of `A`. Does not compute the transform. -/
def hnf (A : Matrix Int n m) : Matrix Int n m

/-- The number of nonzero rows of `hnf A`, i.e. the rank of `A` over `ℤ`. -/
def hnfRank (A : Matrix Int n m) : Nat

/-- The nonzero rows of `hnf A`: the canonical basis of the row lattice,
independent of how many generators `A` supplied. -/
def hnfBasis (A : Matrix Int n m) : Matrix Int (hnfRank A) m

/-- The Hermite normal form with the unimodular transform, the pivot
columns, and the rank, in the shared echelon-data shape. -/
def hnfData (A : Matrix Int n m) : RowEchelonData Int n m

/-- The inverse of `(hnfData A).transform`, accumulated alongside it. -/
def hnfInv (A : Matrix Int n m) : Matrix Int n n

/-- Hermite normal form of a square matrix, by the Domich-Kannan-Trotter
recurrence on `[A; d·I]` when `d = |det A|` is nonzero. -/
def hnfSquare (A : Matrix Int n n) : Matrix Int n n

/-- Integer coefficients expressing `v` as a combination of the rows of
`A`, or `none` when `v` is not in the row lattice. -/
def latticeCoeffs (A : Matrix Int n m) (v : Vector Int m) : Option (Vector Int n)

/-- Decides membership of `v` in the integer row lattice of `A`. -/
def latticeContains (A : Matrix Int n m) (v : Vector Int m) : Bool

/-- A basis of the integer kernel lattice `{x | vecMul x A = 0}`, as the
rows of an `(n - hnfRank A) × n` matrix. -/
def kernelBasis (A : Matrix Int n m) : Matrix Int (n - hnfRank A) n

/-- The pivot entries of `hnf A`, in column order. -/
def pivots (A : Matrix Int n m) : Vector Int (hnfRank A)

/-- The index `[ℤᵐ : L]` of the row lattice of `A`, or `0` when the row
lattice does not have finite index. -/
def latticeIndex (A : Matrix Int n m) : Int

end Hex.Matrix
```

Contracts an implementer would otherwise have to guess. `hnf` and
`hnfData` agree on the form. `hnfRank A` is `(hnfData A).rank` and is
computed without building the transform. `latticeCoeffs` returns
coefficients against the rows of `A`, not against the rows of `hnf A`,
which is why it needs the transform: solve against `hnf A` by
back-substitution with exact division at each pivot, then map the answer
through `(hnfData A).transform`. `kernelBasis` is the last `n - r` rows
of `(hnfData A).transform`, and its dependent type follows `nullspace`
in `hex-row-reduce`, which is already indexed by `rowReduce_rank M`.
`latticeIndex` returns the pivot product when `hnfRank A = m` and `0`
otherwise. The `0` is correct rather than a fallback: a row lattice of
rank below `m` has infinite index in `ℤᵐ`, and `0` is the value `|det|`
already takes in the square case. Note that finite index needs
`hnfRank A = m`, the number of *columns*, so a wide matrix never has one
however many independent rows it has.

`hnfSquare` chooses between the modular algorithm and the general one on
the determinant returned by `hex-bareiss`. Both branches are complete
algorithms, so this is a dispatch and not a total form of a partial
helper in the sense of design principle 8. No fallback classification is
required, and none should be written.

## Correctness theorems

```lean
theorem hnfData_isHNF (A : Matrix Int n m) : IsHNF A (hnfData A)
theorem hnf_eq_hnfData_echelon (A : Matrix Int n m) : hnf A = (hnfData A).echelon
theorem hnfRank_eq (A : Matrix Int n m) : hnfRank A = (hnfData A).rank
theorem hnfInv_mul (A : Matrix Int n m) :
    hnfInv A * (hnfData A).transform = Matrix.identity n
theorem mul_hnfInv (A : Matrix Int n m) :
    (hnfData A).transform * hnfInv A = Matrix.identity n

-- Uniqueness, in the two forms callers want.
theorem IsHNF.eq (h : IsHNF A D) (h' : IsHNF A D') :
    D.rank = D'.rank ∧ D.echelon = D'.echelon
theorem IsHNF.eq_of_memLattice (h : IsHNF A D) (h' : IsHNF B D')
    (hL : ∀ v, A.memLattice v ↔ B.memLattice v) :
    D.rank = D'.rank ∧ D.echelon = D'.echelon
theorem hnf_idem (A : Matrix Int n m) : hnf (hnf A) = hnf A

-- Canonicity across presentations, where the shapes need not agree.
theorem hnfBasis_eq_of_memLattice (A : Matrix Int n m) (B : Matrix Int n' m)
    (hL : ∀ v, A.memLattice v ↔ B.memLattice v) :
    hnfRank A = hnfRank B ∧ HEq (hnfBasis A) (hnfBasis B)

-- Lattice statements.
theorem hnf_memLattice_iff (A : Matrix Int n m) (v : Vector Int m) :
    A.memLattice v ↔ (hnf A).memLattice v
theorem latticeCoeffs_sound {A : Matrix Int n m} {v c} :
    latticeCoeffs A v = some c → vecMul c A = v
theorem latticeCoeffs_complete {A : Matrix Int n m} {v} :
    (∃ c, vecMul c A = v) → (latticeCoeffs A v).isSome
theorem latticeContains_iff {A : Matrix Int n m} {v} :
    latticeContains A v = true ↔ ∃ c, vecMul c A = v

-- Kernel.
theorem kernelBasis_mul (A : Matrix Int n m) : kernelBasis A * A = 0
theorem kernelBasis_complete {A : Matrix Int n m} {x : Vector Int n} :
    vecMul x A = 0 → ∃ c, vecMul c (kernelBasis A) = x

-- Determinant and index.
theorem latticeIndex_eq_prod_pivots (A : Matrix Int n m) (h : hnfRank A = m) :
    latticeIndex A = (pivots A).foldl (· * ·) 1
theorem latticeIndex_eq_det (A : Matrix Int n n) :
    latticeIndex A = ((det A).natAbs : Int)
```

`IsHNF.eq_of_memLattice` is the substantive one and `IsHNF.eq` is its
special case. Everything the library advertises about canonicity at a
fixed shape comes from it, and `hnfBasis_eq_of_memLattice` is what lifts
that across presentations, so those two are the theorems to prove first
and the ones a `sorry` must not survive in.
`kernelBasis_complete` is the saturation statement: it says the returned
rows generate the whole kernel lattice, and it is what a rational
nullspace computation cannot give.

`latticeIndex_eq_det` is the square specialisation of
`latticeIndex_eq_prod_pivots`, and is worth stating separately because it
gives a second determinant algorithm to cross-check `hex-bareiss`
against.

`memLattice` is `Hex.Matrix.memLattice`, currently defined in
`HexLLL/Lattice.lean`. See the next section.

## Certificates and certified dispatch

`hex-lll` already has the machinery this library needs, and it should be
reused rather than reinvented. `Hex.Internal.mulEqCert U A C` decides
`U * A = C` through a Kronecker-substitution digit packing, so the
product matrix is never formed, and `mulEqCert_iff` proves it correct.
`Hex.Matrix.sameLatticeCert` composes two of those into a same-lattice
witness, with `sameLatticeCert_sound`.

The Hermite certificate is three checks:

```lean
/-- Accepts `(H, U, W)` as the Hermite normal form of `A` with transform
`U` and inverse transform `W`. -/
def hnfCert (A H : Matrix Int n m) (U W : Matrix Int n n)
    (r : Nat) (piv : Vector (Fin m) r) : Bool :=
  Hex.Internal.mulEqCert U A H
    && Hex.Internal.mulEqCert U W (Matrix.identity n)
    && isHNFForm H r piv

theorem hnfCert_sound :
    hnfCert A H U W r piv = true → IsHNF A ⟨r, H, U, piv⟩
```

`isHNFForm` is the decidable shape test for the four clauses, written
directly on the entries. Note what the three checks buy. `U * W = I`
over a commutative ring gives `W * U = I` as well, through the adjugate,
so unimodularity of `U` follows from one product check. The reverse
product need not be certified separately. The same-lattice statement
then follows from `U * A = H` and `W * H = W * U * A = A`. So
`sameLatticeCert`'s second check is redundant here and should not be
paid for.

**The certificate is complete, unusually.** The warning at the head of
[future-work](../future-work.md) is that a positive certificate
establishes minimality, uniqueness, or canonicity only when it carries a
separate witness for that property. Hermite normal form is one of the
few cases where no second witness is needed: by `IsHNF.eq`, anything
satisfying the shape clauses with a unimodular transform *is* the
Hermite normal form. An accepted candidate is not merely admissible, it
is the answer.

That makes certified dispatch to an external implementation
straightforward, in exactly the shape `hex-lll`'s `certCheck` already
uses for fpLLL: an untrusted provider returns `(H, U, W)`, `hnfCert`
accepts or rejects it, and the native algorithm runs when the provider
is absent or rejected. Correctness then depends only on `hnfCert_sound`
and the native path, which is what design principle 4 permits. The
provider is **not** part of v1. It is recorded here so the certificate
is designed for it now (the checker takes `W` as an argument rather than
recomputing an inverse, which is the one decision that would be
expensive to change later).

The lemma this rests on is `Hex.Matrix.mul_eq_one_comm` in
`HexDeterminant/Adjugate.lean`:

```lean
theorem mul_eq_one_comm {U W : Matrix R n n} (h : U * W = Matrix.identity n) :
    W * U = Matrix.identity n
```

for a commutative ring, proved through `adjugate_mul` and `mul_adjugate`. It
is adjugate theory rather than Hermite theory, which is why it lives there.

## Prerequisite changes in other libraries

Three small relocations, each with a reason independent of this library.

**`memLattice` should move to `hex-matrix`.** `Hex.Matrix.memLattice b v`
is `∃ c, vecMul c b = v`. It mentions nothing from `hex-lll` and nothing
from `hex-gram-schmidt`, but it lives in `HexLLL/Lattice.lean` alongside
`independent`, which genuinely needs Gram-Schmidt. Every lattice
statement in this SPEC is phrased with it, and `hex-hermite` should not
acquire a dependency on `hex-lll` (and through it `hex-gram-schmidt`,
`hex-bareiss`, `hex-determinant`) to say "is an integer combination of
the rows". Move `memLattice`, `vecMul_mul`, `memLattice_of_mul_eq`, and
`memLattice_iff_of_mul_eq` into `HexMatrix/Lattice.lean`, and leave
`independent` where it is.

**`mulEqCert` should be public.** It is in `Hex.Internal`, so it is
reachable but marked as an implementation detail. The packed product
check is the right primitive for any certificate that asserts a matrix
identity without forming the product, and this library plus `hex-smith`
are two more consumers. Promote it to `Hex.Matrix` next to
`sameLatticeCert`, and move both to `hex-matrix` with `memLattice`.

**`mul_eq_one_comm`** is done: it and the matrix-level `adjugate_mul` are in
`HexDeterminant/Adjugate.lean`, with `smul_mul` added to `hex-matrix`
underneath them.

**`exactDiv` should move to `hex-arith`.** `HexBareiss/Bareiss.lean`
defines the proof-free `exactDiv` with its `@[extern]` binding and proves
`exactDiv_eq_divExact` beside it. This library and `hex-smith` both want
exactly that primitive, and copying it into two more places is how three
slightly different versions appear. It is integer arithmetic, so it
belongs next to `extGcd`, with `hex-bareiss` re-exporting or importing
it.

None of the four blocks starting work here: each can be done as a
separate change before or alongside the first Hermite commit, and until
they are, this library can name the existing paths.

## Why `Int` and not a Euclidean domain class

The obvious generalisation is a class carrying `xgcd`, exact division,
and a normalisation, instantiated at `Int` now and at `FpPoly p` or
`DensePoly` later, which would serve the polynomial-matrix invariant
factors item in [future-work](../future-work.md). This SPEC does not do
that, for a reason worth recording so the question is not reopened
without new information.

The shared part is smaller than it looks. What generalises is the 2x2
elimination step. What does not: the canonical form of a pivot is
"positive" over `ℤ` and "monic" over `F[x]`; the reduction of entries
above a pivot is `%` into `[0, p)` over `ℤ` and remainder of lower
degree over `F[x]`; the termination measure is absolute value in one
case and degree in the other; and the growth problem that motivates
the eager reduction and the modular variant is a coefficient-size problem over
`ℤ` and a degree-growth problem over `F[x]`, with different remedies.
A class that abstracts only the elimination step buys one function and
costs an indirection on a path that has to reduce cheaply. The
generalisation becomes worth doing when the `F[x]` consumer exists and
its normalisation and growth story is written down, not before.
[future-work](../future-work.md) says the same thing in the other
direction: the two items "share an algorithm shape rather than a
theorem".

## Complexity

`A` is `n × m` with rank `r` and entries bounded by `B` in absolute
value. Costs are in ring operations on `Int`, with operand size stated
separately, because the whole design question is operand size.

These are **matrix-update counts**, not worst-case complexity: they count
row updates and `extGcd` calls, each of which is one Euclidean run on
operands of the stated size rather than a constant-time operation. A bit
complexity would be the product of these counts with an operand size that
depends on which algorithm ran, and that product is measured rather than
derived. See "Benchmarking".

| operation | algorithm | matrix updates and `extGcd` calls | operand size |
|---|---|---|---|
| `hnf` | column sweep with eager reduction above each pivot | `O(r · n · m)` | processed part bounded by its own pivots, unprocessed part unbounded |
| `hnfSquare` (nonsingular) | elimination modulo the determinant `d` | `O(n³)` | `< d` throughout |
| `hnfData` | `hnf` plus accumulation of `U` and `W` | `+ O(r · n²)` | larger than `H`; see "Entry growth" |
| `latticeCoeffs` | back-substitution with exact division, then one `vecMul` through `U` | `O(n · m)` | bounded by the entries of `H` and `U` |
| `kernelBasis` | row slice of `U` | none | `U`'s |
| `latticeIndex` | pivot product | `O(m)` | bounded by the index |

## The Mathlib layer

`hex-hermite-mathlib` proves:

```lean
/-- The row lattice is unchanged. -/
theorem span_hnf (A : Matrix Int n m) :
    Submodule.span ℤ (Set.range (matrixEquiv (hnf A))) =
      Submodule.span ℤ (Set.range (matrixEquiv A))

/-- The transform is an element of the general linear group over `ℤ`. -/
theorem isUnit_transform (A : Matrix Int n m) :
    IsUnit (Matrix.det (matrixEquiv (hnfData A).transform))

/-- The integer rank agrees with the rank over `ℚ`. -/
theorem hnfRank_eq_rank (A : Matrix Int n m) :
    hnfRank A = (matrixEquiv A).rank

/-- Integer lattice membership is membership in the span. -/
theorem latticeContains_iff_mem (A : Matrix Int n m) (v : Vector Int m) :
    latticeContains A v = true ↔
      vectorEquiv v ∈ Submodule.span ℤ (Set.range (matrixEquiv A))

/-- The kernel basis is a basis of the kernel submodule. -/
noncomputable def kernelBasisEquiv (A : Matrix Int n m) :
    Module.Basis (Fin (n - hnfRank A)) ℤ
      (LinearMap.ker (Matrix.vecMulLinear (matrixEquiv A)))
```

The last is the payoff and the reason the layer is more than a
restatement: Mathlib's basis for a submodule of a free module over a PID
(`Submodule.basisOfPid`) is noncomputable, and this supplies an
executable one for the kernel of an integer matrix, with the identity
between them proved. `hex-smith` extends the same idea to
`Module.Basis.SmithNormalForm`.

Mathlib has no Hermite normal form for matrices (searching for `hermite`
finds Hermite polynomials, the Hermite-Minkowski theorem, and
`IsHermitian`, none of them this). So there is nothing to correspond
with, and the correspondence statements are all against `Submodule.span`,
`Matrix.rank`, and `LinearMap.ker`. Upstreaming the definition and the
uniqueness theorem is a reasonable later goal and is out of scope here.

Following the project split, the uniqueness theorem `IsHNF.eq` is
Mathlib-free and proved in `hex-hermite`: it is a statement about the
executable types with an elementary proof by induction on the pivot
columns, and no part of it is shorter through Mathlib.

## Conformance

Per [SPEC/testing.md](../testing.md). This library **extends the
existing matrix oracle rather than adding one**: `scripts/oracle/matrix_flint.py`
already serves `HexRowReduce`, `HexDeterminant`, and `HexBareiss`, and
already reads the `matrix` fixture kind emitted by
`Hex/Conformance/Emit.lean`'s `emitMatrixFixture`. Adding Hermite normal
form means two new handlers in that driver's `handlers` table (`hnf` and
`hnf-transform`), a new emit driver
`conformance/HexHermite/EmitFixtures.lean` exposed as
`lean_exe hexhermite_emit_fixtures`, a committed snapshot at
`conformance-fixtures/HexHermite/hermite.jsonl`, and one tuple appended
to `ORACLES` in `scripts/ci/run_oracles.sh`:

```
"HexHermite|hexhermite_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexHermite/hermite.jsonl"
```

No new job, no matrix, no new workflow file, per [SPEC/CI.md](../CI.md).

**Oracle choice.** python-flint is already the driver's oracle and FLINT
exposes `fmpz_mat_hnf` and `fmpz_mat_hnf_transform` in the row-style
convention this SPEC fixes. The python-flint binding for the
transform-returning form must be confirmed against the version CI
installs before the driver is written. If it is not exposed, the
fallback is PARI's `mathnf(M, 1)` through `cypari2`, which is already a
CI dependency. The column-style-to-row-style conversion is then done in
the driver, and it is not just a transpose: reversing rows or columns on
its own changes the ambient coordinates and is not lattice-preserving.
With `J_k` the `k × k` reversal matrix, run PARI on `J_m Aᵀ`, convert its
`m × r` result `H'` by `J_r H'ᵀ J_m`, and append `n - r` zero rows. That
mapping is itself a thing to test, on rectangular and rank-deficient
fixtures, before it is trusted to report a mismatch.

Whichever oracle is used, the driver checks the *form* against it and
checks the *transform* by the identity `U * A = H` rather than against
the oracle's `U`, because `U` is not unique and comparing it would
produce spurious failures.

**Cases that must be present**, since these are what a plausible
implementation gets wrong:

- the zero matrix, and a matrix with a zero column at the left, where
  the first pivot is not in column `0`;
- rank-deficient input, including duplicated and negated rows, checking
  that the zero rows land at the bottom and `rank` is right;
- more rows than columns and more columns than rows;
- negative entries in every position that feeds a pivot, since the sign
  handling of `extGcd` and of `%` is where an implementation goes wrong;
- an input already in Hermite normal form, checking idempotence;
- a pivot of `1`, where the reduction above it must produce zeros;
- an input whose naive elimination blows up (a random `20 × 20` matrix
  with entries in `[-10, 10]` is enough) with the entry sizes of the
  intermediate matrices recorded, so the growth claim under "Entry
  growth" is checked rather than asserted;
- two matrices with the same row lattice and different numbers of rows,
  checking that their `hnfBasis` values agree. This case is on
  `hnfBasis`, not on `hnf`, because `hnf` of an `n × m` and an `n' × m`
  matrix are different types and differ in their trailing zero rows;
- for `hnfSquare`, an input whose Hermite normal form contains a pivot
  equal to `d = |det A|` (the `1 × 1` matrix `[2]` is the smallest), which
  is the case that catches a modular implementation reducing that pivot to
  zero.

The property checks in `conformance/HexHermite/Conformance.lean` assert
`U * A = H`, `U * W = I`, the four shape clauses, the pivot product
against `hex-bareiss`'s determinant on square nonsingular input,
`latticeContains` on both a member and a non-member of the lattice, and
`kernelBasis A * A = 0`.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), with drivers at
`bench/HexHermite/Bench.lean`. The bench must not import Mathlib.

**Input families.** Growth behaviour depends on the input in a way that
a single family would hide:

- `random-dense-hermite`: uniform entries in `[-B, B]`, square and
  nonsingular, the case where the modular algorithm should win.
- `rank-deficient-hermite`: rows drawn as integer combinations of a
  smaller independent set, where the determinant is zero and the modular
  path is unavailable.
- `tall-hermite`: many more rows than columns, the shape a number-field
  module basis has, where most rows are redundant.
- `unimodular-conjugate`: `V * D` for a random unimodular `V` and a
  diagonal `D` with known entries, so the expected form is known in
  advance and the input can be made arbitrarily badly conditioned
  without a large determinant.

**Comparators.** FLINT `fmpz_mat_hnf` through python-flint, and PARI
`mathnf` through `cypari2`, both `informational`. FLINT dispatches
across several algorithms including `hnf_pernet_stein`, which is
asymptotically faster than anything specified here, so the ratio
measures a different algorithm and does not hold a required threshold.
PARI is column-style and its timing includes the convention conversion.
Both are recorded for orientation in
`reports/hex-hermite-performance.md`.

**Two decision rules written down in advance.** Both are stated over a
range rather than at one ladder endpoint, because a single-point ratio
mostly reports where the crossover was placed.

1. `hnfSquare` (modular) is kept only if it beats the default over a
   named production range: the crossover curve in dimension and entry
   bit-size is measured, and the modular path must win across the whole
   upper half of both ladders, not merely at the last rung. If the
   crossover sits outside the sizes the named consumers produce, the
   modular path is not carrying its complexity and should be removed
   rather than kept as an unmeasured alternative.
2. The LLL-based Havas-Majewski-Matthews algorithm is justified only if
   growth rather than operation count is what limits the default. The
   evidence is a divergence: the peak intermediate entry bit-size must
   grow faster in the dimension than the output entry bit-size does on
   `unimodular-conjugate`, with the time spent in big-integer arithmetic
   rising as a share of total time. Instrument entry size and allocation
   in the bench, not just wallclock. A time ratio alone cannot separate
   these two causes.

## File organisation

```
HexHermite/
  Contracts.lean     -- IsHNF, isHNFForm, IsHNF.det_transform
  Step.lean          -- the 2x2 elimination step, its inverse, exact division
  Hermite.lean       -- hnf, hnfData, hnfInv, hnfRank, hnfBasis
  Modular.lean       -- hnfSquare, the DKT recurrence on [A; d·I]
  Unique.lean        -- IsHNF.eq, IsHNF.eq_of_memLattice, hnf_idem
  Lattice.lean       -- latticeCoeffs, latticeContains, kernelBasis, latticeIndex
  Cert.lean          -- hnfCert and its soundness
HexHermite.lean      -- umbrella
HexHermiteMathlib/
  Span.lean          -- span and lattice correspondence
  Rank.lean          -- hnfRank = Matrix.rank
  Kernel.lean        -- the executable kernel basis as a Module.Basis
HexHermiteMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexHermite:
    deps: [HexRowReduce, HexArith, HexBareiss]
    mathlib: false
    done_through: 0
    status: draft
  HexHermiteMathlib:
    deps: [HexHermite, HexRowReduceMathlib, HexBareissMathlib]
    mathlib: true
    done_through: 0
    status: draft
```

`HexRowReduce` supplies `RowEchelonData` and `IsEchelonForm`, `HexArith`
supplies `extGcd`, and `HexBareiss` supplies the determinant for the
modular algorithm and (through `HexDeterminant`) `det_mul` and the
adjugate identities. `HexMatrix` arrives through all three.

## Open questions

- **Where the rectangular modular algorithm stops.** The modular
  argument needs `d·ℤᵐ ⊆ L` for the row lattice `L ⊆ ℤᵐ`, which needs `L`
  to have finite index, which needs `hnfRank A = m`: full **column**
  rank, with `n ≥ m`. It is not full row rank. A wide matrix with
  independent rows spans a lower-rank sublattice of `ℤᵐ` and admits no
  such `d` at all, so the modular path is unavailable there however many
  independent rows it has. For `n ≥ m` of full column rank, the
  determinant of any nonsingular `m × m` row submatrix is a positive
  multiple of the index and is a valid modulus. Whether that extra
  machinery pays is a benchmark question against `tall-hermite`, and
  until it is answered `hnfSquare` is the only modular entry point.
- **Whether the rank-profile preprocessing is worth writing.** The
  default algorithm is total but its unprocessed rows are unbounded. The
  Kannan-Bachem arrangement bounds them, at the cost of rank-profile
  preprocessing, a full-rank subproblem, and reconstruction of the zero
  rows and the transform. That is a real algorithm to specify, not a
  variant of the default, and it should be specified only if the entry
  instrumentation under "Benchmarking" shows the unprocessed rows are
  what hurts.
- **Whether `hnfData` should return `W`.** This SPEC returns the inverse
  transform from a separate function, `hnfInv`, so that `RowEchelonData`
  is unchanged. The alternative is a Hermite-specific data structure
  carrying both. The existing shape is preferred because it keeps the
  span and column-partition operations in `hex-row-reduce` usable
  directly, but if the two are always called together the extra
  traversal is waste and the structure should be reconsidered.
- **Kernel reduction.** Nothing in this SPEC is on a `decide +kernel`
  path today. If the Hermite certificate is ever checked in the kernel,
  the exposure analysis in the `hex-mv-poly` SPEC applies verbatim, and
  the `Vector.ofFn` and derived-`DecidableEq` traps recorded in
  `progress/lean4-array-decidableeq-module-repro.md` will need the same
  treatment.
