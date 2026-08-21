# hex-smith (Smith normal form over `Int`, depends on hex-hermite)

The Smith normal form of an integer matrix: a diagonal matrix `S` with
`S = U * A * V` for unimodular `U` and `V`, whose diagonal entries are
positive and form a divisibility chain `d₁ ∣ d₂ ∣ ⋯ ∣ d_r`. Those
entries are the invariant factors of `A`, and they determine the
structure of the abelian group presented by `A`. Mathlib-free; the
companion `hex-smith-mathlib` builds Mathlib's
`Module.Basis.SmithNormalForm` from the executable output and relates
the invariant factors to the structure theorem for finitely generated
modules over a PID.

This SPEC is the second half of a pair with
[hex-hermite](hex-hermite.md), which fixes the conventions, the
unimodular certificate shape, the entry-growth analysis, and the oracle
this library extends. Read that one first.

## Why this library exists

Hermite normal form already decides membership, produces one solution of
`vecMul x A = b`, gives the integer kernel, and computes the index. Smith
normal form adds canonical invariant factors and simultaneous source/target
coordinates. Its genuinely new uses are:

- **The structure of a finitely generated abelian group.** Given
  relations as the rows of `A : Matrix Int n m`, the group
  `ℤᵐ / rowlattice A` is `ℤ^(m - r) ⊕ ℤ/d₁ ⊕ ⋯ ⊕ ℤ/d_r`, read directly
  off the diagonal, with the `dᵢ = 1` summands dropped. This is the
  headline consumer and the reason the divisibility chain matters:
  without it the diagonal is not canonical and the summands are not the
  invariant factors.
- **Diagonal coordinates for integer linear systems.** The existing
  `latticeCoeffs` API remains the efficient way to obtain one solution.
  Smith data additionally proves that solvability is a coordinatewise
  divisibility/zero test after applying `V`, and exposes both changes of
  basis for consumers that need the diagonal presentation itself.
- **A canonical factorisation of the index.** Hermite already computes the
  index. Smith proves that a finite index is `∏ dᵢ`, recording how that
  order decomposes rather than introducing a second index algorithm.
- **Invariant factors of a module map**, which is what the polynomial
  matrix item in [future-work](../future-work.md) wants over `F[x]`
  rather than `ℤ`. That item is not this library; see "Why `Int`" in
  [hex-hermite](hex-hermite.md).

The dependency on `hex-hermite` is real rather than organisational: the
`extGcd` elimination step with its explicit inverse, the exact-division
discipline, the certificate machinery, the conventions, and the
`mul_eq_one_comm` obligation are all shared. Note that the default
algorithm below does *not* call `hnf`; the Kannan-Bachem variant under
"Open questions" would, which is the other reason to keep the two
libraries adjacent.

## What Smith normal form is

`A : Matrix Int n m`. A **Smith normal form** of `A` is a triple
`(U, S, V)` with `U : Matrix Int n n` and `V : Matrix Int m m`
unimodular and `S = U * A * V` satisfying:

1. `S[i][j] = 0` whenever `i ≠ j`.
2. `S[i][i] = dᵢ > 0` for `i < r`, and `S[i][i] = 0` for `i ≥ r`.
3. `dᵢ ∣ dᵢ₊₁` for `i + 1 < r`.

`S` is unique. `U` and `V` are not, and are much less determined than
the Hermite transform is: any automorphism of the source or target
lattice compatible with the diagonal can be composed in. No uniqueness
theorem for `U` or `V` is stated.

Uniqueness of `S` is not a shape argument, and this is the one place
where Smith normal form needs an idea that Hermite normal form does not.
The invariant is the **`k`-th determinantal divisor** `D_k(A)`, the gcd
of all `k × k` minors of `A`. Every `k × k` minor of `U * A` is an
integer combination of the `k × k` minors of `A` (this is Cauchy-Binet
in its general rectangular form), so `D_k` is unchanged by multiplying
by a unimodular matrix on either side. For a diagonal matrix with a
divisibility chain, `D_k = d₁ ⋯ d_k` for `k ≤ r`, with `D_0 = 1` and
`D_k = 0` for `k > r`. Hence `r` is the largest `k` with `D_k ≠ 0`, and
`d_k = D_k(A) / D_{k-1}(A)`, both determined by `A` alone.

Stating the `k > r` case is not pedantry: it is what makes the rank part
of uniqueness provable, and leaving it out breaks the argument. See
`IsSNF.detDivisor_eq` under "Correctness theorems".

That argument is also the specification: `D_k` is what the library
proves its output computes, and every uniqueness and canonicity claim
comes from it.

## Data and contract

```lean
/-- Executable Smith normal form data: the rank, the invariant factors,
and both change-of-basis matrices with their inverses. -/
structure SmithData (n m : Nat) where
  rank : Nat
  diag : Vector Int rank
  left : Matrix Int n n
  leftInv : Matrix Int n n
  right : Matrix Int m m
  rightInv : Matrix Int m m

/-- Prerequisite API from `HexMatrix/Diagonal.lean`: the `n × m` matrix
carrying `d` down the leading diagonal. -/
def diagMatrix {r : Nat} (d : Vector Int r) (n m : Nat) : Matrix Int n m :=
  Matrix.ofFn fun i j => if h : i.val = j.val ∧ i.val < r then d[i.val]'h.2 else 0

/-- Smith normal form contract. -/
structure IsSNF {n m : Nat} (A : Matrix Int n m) (S : SmithData n m) : Prop where
  left_inv : S.left * S.leftInv = Matrix.identity n
  right_inv : S.right * S.rightInv = Matrix.identity m
  mul_eq : S.left * A * S.right = diagMatrix S.diag n m
  rank_le_n : S.rank ≤ n
  rank_le_m : S.rank ≤ m
  diag_pos : ∀ i : Fin S.rank, 0 < S.diag[i]
  chain : ∀ (i : Nat) (h : i + 1 < S.rank), S.diag[i]'(by omega) ∣ S.diag[i + 1]
```

This elaborates as written against the current tree. Three decisions in
it are worth stating, because an implementer would otherwise choose
differently.

**One-sided inverse fields.** `left_inv` and `right_inv` record only
`U * W = I` and `V * X = I`. The other side follows over a commutative
ring through the adjugate, by the `mul_eq_one_comm` lemma
[hex-hermite](hex-hermite.md) asks `hex-determinant` for. Carrying both
directions as fields would make every construction discharge a
redundant obligation.

**The inverses are data on the full path, not on the form-only path.** Every
elementary step has an explicit inverse, so `snfData` accumulates `W` and `X`
alongside `U` and `V`. For a left row step `U' = E * U`, update
`W' = W * E⁻¹`; for a right column step `V' = V * F`, update
`X' = F⁻¹ * X`. The public `snf` and `snfRank` paths accumulate none of
these four matrices.

**`diagMatrix` moves to `hex-matrix` before this library starts.** It is a
general constructor and is also used by the Mathlib bridge and tests. The
signature above is the prerequisite API; `hex-smith` does not own a second
copy.

## Algorithms

**The default is the classical Euclidean pivot algorithm**, and it is
called that rather than Kannan-Bachem. Kannan-Bachem controls growth by
alternating row and column Hermite normal forms on trailing submatrices,
and its entry bound comes from that repetition; the pivot loop below does
not inherit those bounds merely by shrinking the pivot, and saying it
does would be an unearned claim. What the loop below has is a
straightforward correctness argument and a termination measure. What it
does not have is a proven entry bound, and both row and column operations
feed the growth here, so it is worse in that respect than the Hermite
case. The benchmark instrumentation under "Benchmarking" is therefore not
optional decoration: it is the only evidence about growth this algorithm
comes with.

Specifying Kannan-Bachem properly (the alternating Hermite calls, the
block embeddings, rank-deficient handling, and transform accumulation
through all of it) is a separate piece of work, listed under "Open
questions" as the optimisation to measure against this default.

The pivot loop, which is where the mathematics lives:

1. If the remaining block is zero, stop with the current rank.
2. Move a nonzero entry of minimal absolute value to the pivot position
   by one row swap and one column swap.
3. Clear the pivot's column with row operations and its row with column
   operations, using the same `extGcd` 2x2 step as
   [hex-hermite](hex-hermite.md). Each step replaces the pivot by
   `gcd(pivot, entry)`, so the pivot never grows.
4. If the pivot is negative, negate its row. On the full-data path also
   negate the matching row of `U` and column of `W`; the row-negation matrix
   is its own inverse. Perform this inline without a recursive call; it leaves
   both components of the termination measure below unchanged.
5. If some entry `a[i][j]` of the remaining block is not divisible by
   the pivot `p`, add row `i` to the pivot row **and immediately run the
   column-`j` elimination against the new entry**, which replaces `p` by
   `gcd(p, a[i][j])`, then return to step 3. This is the step that
   produces the divisibility chain, and it is the step a naive
   implementation omits.
6. Otherwise advance to the next diagonal position.

**Termination measure.** The pair `(|pivot|, c)` ordered
lexicographically, where `c` is the number of nonzero entries in the
pivot row and column other than the pivot itself. Step 3 either leaves
`|pivot|` fixed and decreases `c` (when the pivot divides the entry, so
the step is a plain subtraction) or strictly decreases `|pivot|` (when
it does not).

Step 5 is why it is stated as one fused step rather than two. Adding row
`i` to the pivot row on its own decreases nothing: `|pivot|` is unchanged
and `c` rises from `0`, so the measure *increases*, and "it decreases on
the next pass" is not a termination argument, since Lean needs the
recursive call itself to decrease. Fusing the elimination into the same
step fixes it: the recursion happens only after the pivot has become
`gcd(p, a[i][j])`, which is a strict divisor of `p` because `p ∤ a[i][j]`,
so `|pivot|` strictly decreases across the whole step. Both components
are naturals, so the loop is well-founded.

Whether that measure is threaded as a `termination_by` clause or as
explicit fuel with a sufficiency theorem is an implementation decision,
but it must be one of the two. `hex-lll` sets the precedent for the fuel
form (`lllFuel`, with the sufficiency theorem tracked as separate work),
and the same discipline applies: the fuel-exhausted branch returns a
value that a sufficiency theorem proves unreachable on public API
inputs, and that classification is written down. Design principle 8
allows nothing weaker.

**The modular variant is not a v1 declaration.** Iliopoulos's algorithm
runs elimination modulo a positive multiple of the largest invariant
factor, applies to nonsingular square input, and computes only the diagonal;
multiplier reconstruction is a separate algorithm. Those facts do not
specify its recurrence, modulus invariant, singular classification, or
agreement theorem. V1 therefore has no `snfSquareDiag` or `Modular.lean`.
A future proposal must give the complete algorithm and prove that its `some`
result equals `invariantFactors` and that `none` is equivalent to singularity
before adding a public declaration.

**A fast path for diagonal input.** A diagonal matrix is already almost
in Smith normal form and needs only normalisation and the chain. The
normalisation is not skippable, because the input diagonal may contain
zeros and negatives: negate each negative entry, move the nonzero entries
stably before the zeros, and take the rank to be the number of nonzero
entries. `snfDiagonalData` accumulates the corresponding row and column
operations and their inverses; form-only `snfDiagonal` does not. The gcd
and lcm sweep then
runs on the positive prefix alone, which is what makes the divisions by
`g` below defined: `[0, 0]` has no `g` to divide by, and `[0, 2]` is not
in Smith normal form despite being diagonal.

For two adjacent normalised entries `a, b > 0` with
`(g, s, t) := extGcd a b` and `l = a * b / g`, the pair

```
L = ⎡ 1     1 ⎤ then ⎡     1      0 ⎤     V = ⎡ s   -b/g ⎤
    ⎣ 0     1 ⎦      ⎣ -b·t/g     1 ⎦         ⎣ t    a/g ⎦
```

sends `diag(a, b)` to `diag(g, l)`: adding the second row to the first
gives `[[a, b], [0, b]]`, right-multiplying by `V` (which has
determinant `(s·a + t·b)/g = 1`) gives `[[g, 0], [b·t, l]]`, and the
second row operation clears the `b·t` entry, which is divisible by `g`
because `g` divides `b`. Run a fixed bubble network of `r` full adjacent
passes. On each prime valuation, `(gcd, lcm)` is `(min, max)`, so the same
network sorts every valuation and yields the divisibility chain after at
most `r · (r - 1)` pair steps. This fixed schedule makes both termination
and the `O(r²)` bound immediate. This is FLINT's
`snf_diagonal`, and it is the path a direct-sum presentation of an
abelian group takes, which is the common case for the headline consumer.

**Not specified: Storjohann's algorithms.** The asymptotically fast
methods based on matrix multiplication are out of scope, and the
comparator classification under "Benchmarking" says so rather than
pretending the ratio against FLINT measures the same algorithm.

## API

```lean
namespace Hex.Matrix

/-- Named structure-theorem data for `ℤᵐ / rowlattice A`. -/
structure AbelianStructure where
  freeRank : Nat
  torsionFactors : Array Nat

/-- The canonical `n × m` Smith matrix. Does not compute transforms. -/
def snf (A : Matrix Int n m) : Matrix Int n m

/-- The number of nonzero diagonal entries of `snf A`. -/
def snfRank (A : Matrix Int n m) : Nat

/-- Smith form with all four change-of-basis matrices. -/
def snfData (A : Matrix Int n m) : SmithData n m

/-- The invariant factors of `A`, positive and in a divisibility chain. -/
def invariantFactors (A : Matrix Int n m) : Vector Int (snfRank A)

/-- Form-only Smith normal form of a diagonal matrix. -/
def snfDiagonal {r : Nat} (d : Vector Int r) : Matrix Int r r

/-- Smith normal form data of a diagonal matrix, including transforms. -/
def snfDiagonalData {r : Nat} (d : Vector Int r) : SmithData r r

/-- The structure of `ℤᵐ / rowlattice A`: the free rank, and the
torsion invariants in a divisibility chain with the units dropped. -/
def abelianStructure (A : Matrix Int n m) : AbelianStructure

/-- The `k`-th determinantal divisor: the gcd of the `natAbs` values of
the determinants of all `k × k` submatrices of `A`, taken over every
choice of `k` rows and `k`
columns. `detDivisor A 0 = 1`, and `detDivisor A k = 0` when
`k > min n m` or when every such minor vanishes.

This is the specification function. Its definition is the gcd above and
mentions nothing about `snf`; `IsSNF.detDivisor_eq` is what says the
invariant factors compute it. -/
noncomputable def detDivisor (A : Matrix Int n m) (k : Nat) : Nat

end Hex.Matrix
```

Contracts to state explicitly. `snf`, `snfRank`, `invariantFactors`, and
`abelianStructure` use a form-only engine and allocate no transform matrix.
`snfData` runs the same deterministic pivot choices while accumulating all
four transforms, and its diagonal matrix and rank agree with the form-only
results. `invariantFactors` drops nothing, so its leading entries may be `1`;
`abelianStructure.torsionFactors` converts the entries greater than `1` to
`Nat`, and `freeRank = m - snfRank A`.
The form-only definitions must not be projections of `snfData`: eager
evaluation would allocate the discarded transforms. Implement the general
pivot loop once, parameterised by a companion accumulator that is `Unit` for
`snf` and `(U, W, V, X)` for `snfData`; likewise parameterise the fixed
diagonal network by `Unit` versus the four transforms. Inline the accumulator
operations so the `Unit` instances allocate no matrices. Agreement then comes
from accumulator-parametric step lemmas rather than duplicated correctness
inductions.

There is deliberately no second integer solver or quotient-order function in
this library. `latticeCoeffs` and `latticeIndex` in `hex-hermite` already own
those executable operations. Smith supplies the diagonal solvability theorem
and invariant-factor product theorem below. In particular, for
`S = snfData A`, a transformed right-hand side `bV` is solvable exactly when
its first `S.rank` coordinates are divisible by the corresponding diagonal
entries and every remaining coordinate is zero. Omitting the trailing zero
test is the Smith analogue of omitting Hermite's final residual check.

`detDivisor` is `noncomputable` under design principle 11: its definition
enumerates exponentially many minors and there is no runtime twin. It is
**defined by that enumeration and not through `snf`**. Defining it
through `snf` would make `IsSNF.detDivisor_eq` circular, since the
invariant used to prove that `snf`'s output is canonical would already
contain that output. The executable route to its *value* is the product
of the first `k` invariant factors, which is what `IsSNF.detDivisor_eq`
states. It returns `Nat` so that "the gcd" needs no separate
normalisation clause.

## Correctness theorems

```lean
theorem snfData_isSNF (A : Matrix Int n m) : IsSNF A (snfData A)
theorem snf_eq_data (A : Matrix Int n m) :
    snf A = diagMatrix (snfData A).diag n m
theorem snfRank_eq_data (A : Matrix Int n m) :
    snfRank A = (snfData A).rank
theorem snf_idem (A : Matrix Int n m) : snf (snf A) = snf A
theorem snfRank_le_n (A : Matrix Int n m) : snfRank A ≤ n
theorem snfRank_le_m (A : Matrix Int n m) : snfRank A ≤ m
theorem invariantFactors_pos (A : Matrix Int n m) (i : Fin (snfRank A)) :
    0 < (invariantFactors A)[i]
theorem invariantFactors_chain (A : Matrix Int n m) (i : Nat)
    (h : i + 1 < snfRank A) :
    (invariantFactors A)[⟨i, by omega⟩] ∣
      (invariantFactors A)[⟨i + 1, h⟩]

theorem snfDiagonalData_isSNF {r : Nat} (d : Vector Int r) :
    IsSNF (diagMatrix d r r) (snfDiagonalData d)
theorem snfDiagonal_eq_data {r : Nat} (d : Vector Int r) :
    snfDiagonal d = diagMatrix (snfDiagonalData d).diag r r
theorem snfDiagonal_eq_snf {r : Nat} (d : Vector Int r) :
    snfDiagonal d = snf (diagMatrix d r r)

-- The determinantal-divisor characterisation, which is the specification.
-- Stated for every k, including k > S.rank, where both sides are zero.
theorem IsSNF.detDivisor_eq {A : Matrix Int n m} {S : SmithData n m}
    (h : IsSNF A S) (k : Nat) :
    detDivisor A k =
      if k ≤ S.rank then ((S.diag.take k).foldl (· * ·) 1).natAbs else 0

-- Uniqueness, in the form callers use.
theorem IsSNF.rank_eq (h : IsSNF A S) (h' : IsSNF A S') : S.rank = S'.rank
theorem IsSNF.diag_eq (h : IsSNF A S) (h' : IsSNF A S') (i : Nat)
    (hi : i < S.rank) (hi' : i < S'.rank) : S.diag[i] = S'.diag[i]
theorem IsSNF.form_eq (h : IsSNF A S) (h' : IsSNF A S') :
    diagMatrix S.diag n m = diagMatrix S'.diag n m

-- Agreement with the Hermite rank, and with the determinant.
theorem IsSNF.rank_eq_hnfRank (h : IsSNF A S) : S.rank = hnfRank A
theorem snfRank_eq_hnfRank (A : Matrix Int n m) : snfRank A = hnfRank A
theorem prod_invariantFactors (A : Matrix Int n n) (h : snfRank A = n) :
    (invariantFactors A).foldl (· * ·) 1 = Int.ofNat ((det A).natAbs)

-- The consumer-facing statements.
theorem solvable_iff_diagonal {A : Matrix Int n m} {S : SmithData n m}
    (hS : IsSNF A S) {b : Vector Int m} :
    (∃ x, vecMul x A = b) ↔
      ∃ z, vecMul z (diagMatrix S.diag n m) = vecMul b S.right
theorem solvable_iff_dvd {A : Matrix Int n m} {S : SmithData n m}
    (hS : IsSNF A S) (b : Vector Int m) :
    (∃ x, vecMul x A = b) ↔
      (∀ i : Fin S.rank,
          S.diag[i] ∣ (vecMul b S.right)[
            ⟨i.val, Nat.lt_of_lt_of_le i.isLt hS.rank_le_m⟩]) ∧
      (∀ j : Fin m, S.rank ≤ j.val → (vecMul b S.right)[j] = 0)
theorem latticeIndex_eq_invariantFactors (A : Matrix Int n m) :
    latticeIndex A =
      if snfRank A = m then
        (invariantFactors A).foldl (fun acc d => acc * d.natAbs) 1
      else 0
```

`IsSNF.detDivisor_eq` is the theorem to prove first, and it must be
stated for every `k` rather than only for `k ≤ S.rank`. The `k ≤ S.rank`
form cannot prove `rank_eq`: if `S.rank < S'.rank`, the value that
separates them is `k = S.rank + 1`, which is exactly where the restricted
statement does not apply. With the all-`k` form, `S.rank` is the largest
`k` whose determinantal divisor is nonzero, which gives `rank_eq`, and
cancelling the positive product of the preceding factors gives
`diag_eq`. Everything the library claims about canonicity rests on it.
`IsSNF.form_eq` packages the dependent rank and diagonal equalities into the
fixed `n × m` matrix equality callers usually want. It also proves
`snfDiagonal_eq_snf`: the diagonal-specific data and the general data both
satisfy `IsSNF` for the same input, while `snfDiagonal_eq_data` and
`snf_eq_data` connect the two form-only paths to those data.

**Its prerequisite is a phase of work in `hex-determinant`, and that
work does not exist.** The argument needs each `k × k` minor of a product
to expand as an integer combination of the `k × k` minors of the factors,
that is, Cauchy-Binet in its general rectangular form. What is actually
in the tree is narrower than that in both files. `HexDeterminant/Minor.lean`
provides only `deleteRowCol`, which removes one row and one column from a
square matrix. `HexDeterminant/CauchyBinet.lean` builds
`columnTupleMatrix`, which selects `n` columns from a matrix that has
exactly `n` rows, so the row side is never chosen. `HexMatrix/Submatrix.lean`
offers `principalSubmatrix`, `takeRows`, and `takeCols`, all of which take
prefixes rather than arbitrary index sets. There is no arbitrary
`k`-row-by-`k`-column minor anywhere, and no enumeration of `k`-subsets.

So `hex-determinant` needs, as a named prerequisite:

- selected submatrices indexed by a pair of strictly increasing index
  maps, with the `Fin k` reindexing lemmas;
- enumeration of the `k`-subsets of `Fin n` in a canonical order, which
  is the row-side analogue of the existing `columnTupleVectors`;
- Cauchy-Binet for a selected minor of a product;
- the gcd and divisibility lemmas that turn that expansion into
  invariance of `detDivisor` under unimodular multiplication.

The same selected-minor infrastructure closes `IsSNF.rank_eq_hnfRank`
without importing Mathlib. If `r = hnfRank A`, the HNF pivot rows and pivot
columns select a triangular `r × r` minor with nonzero determinant, while
every `(r + 1) × (r + 1)` minor vanishes because the remaining HNF rows are
zero. Invariance under the HNF transform transfers those statements back to
`A`; the all-`k` Smith characterisation then identifies `S.rank` with `r`.

The executable pivot loop can be prototyped after Hermite lands, but the
library cannot be activated or claim canonical output until this prerequisite
and `IsSNF.detDivisor_eq` are complete. Schedule the determinant work before
the Smith proof phase rather than treating uniqueness as optional follow-up.

## Certificates

The same shape as [hex-hermite](hex-hermite.md), with one more product:

```lean
/-- Accepts `(S, U, W, V, X, T)` as a Smith normal form of `A`, where
`T = U * A` is the intermediate product. -/
def snfCert (A : Matrix Int n m) (S : SmithData n m) (T : Matrix Int n m) : Bool :=
  Hex.Matrix.mulEqCert S.left A T
    && Hex.Matrix.mulEqCert S.right.transpose T.transpose
          (diagMatrix S.diag n m).transpose
    && Hex.Matrix.mulEqCert S.left S.leftInv (Matrix.identity n)
    && Hex.Matrix.mulEqCert S.right S.rightInv (Matrix.identity m)
    && isSNFShape S

theorem snfCert_sound : snfCert A S T = true → IsSNF A S
```

`mulEqCert` checks left multiplication only, so the right-hand product
`T * V = S` is checked in transposed form. The intermediate `T` is an
argument rather than a computed value so that no product matrix is
formed inside the checker, which is the property `mulEqCert` exists to
provide.

As with Hermite normal form, and unlike most items in
[future-work](../future-work.md), **this certificate is complete**: by
`IsSNF.rank_eq` and `IsSNF.diag_eq`, anything satisfying the shape
clauses with unimodular transforms has the rank and the diagonal of the
Smith normal form, so an accepted candidate is the answer and no second
witness for canonicity is needed. Note that this completeness is
downstream of the uniqueness theorem, which is downstream of the
`hex-determinant` prerequisite above; until that chain is closed, the
checker is sound but the "it is the answer" claim is not yet proved.
That makes certified dispatch to an external implementation possible in
the shape `hex-lll`'s `certCheck` already uses. It is not part of v1.

## The Mathlib layer

`hex-smith-mathlib` proves:

```lean
/-- The executable Smith normal form as Mathlib's structure, for the
submodule spanned by the rows of `A`. -/
noncomputable def smithNormalForm (A : Matrix Int n m) :
    Module.Basis.SmithNormalForm
      (Submodule.span ℤ (Set.range (matrixEquiv A))) (Fin m) (snfRank A)

/-- The divisibility chain, which Mathlib's structure does not carry. -/
theorem smithNormalForm_chain (A : Matrix Int n m) (i : Nat) (h : i + 1 < snfRank A) :
    (smithNormalForm A).a ⟨i, by omega⟩ ∣ (smithNormalForm A).a ⟨i + 1, h⟩

/-- The structure theorem, instantiated at the executable output. -/
noncomputable def quotientEquiv (A : Matrix Int n m) :
    (Fin m → ℤ) ⧸ Submodule.span ℤ (Set.range (matrixEquiv A)) ≃ₗ[ℤ]
      (Fin (m - snfRank A) → ℤ) ×
        ⨁ i : Fin (snfRank A), ℤ ⧸ Ideal.span {(invariantFactors A)[i]}
```

Two things are worth knowing about the Mathlib side before this is
scheduled.

**Mathlib's `Module.Basis.SmithNormalForm` does not carry the
divisibility chain.** Its fields are `bM`, `bN`, `f`, `a`, and `snf`,
where `snf : ∀ i, (bN i : M) = a i • bM (f i)`. Nothing constrains `a i`
to divide `a (i+1)`, so the structure is a simultaneous-basis statement
rather than an invariant-factor statement, and its `a` is not canonical.
Mathlib has no invariant factors, no determinantal divisors, and no
elementary divisors anywhere (searching for those terms finds nothing).
So `smithNormalForm_chain` is genuinely new content rather than a
transport, and the executable library is the only source of canonicity.

**The construction is also the first executable one.**
`Submodule.smithNormalForm` is noncomputable and produced by an
existence argument over a PID. Supplying an executable witness with the
identity proved is the same payoff `hex-hermite`'s `kernelBasisEquiv`
delivers, one level up.

The pinned Mathlib quotient helper directly covers only a full-rank
submodule. The displayed `quotientEquiv` is rank-general: its proof must use
the explicit Smith ambient basis, split the complement of the leading
`Fin (snfRank A)` embedding to produce the free factor, and apply the cyclic
quotient equivalence on the occupied coordinates. It is not merely an
application of the existing full-rank helper.

Upstreaming the chain field to Mathlib's structure, or adding invariant
factors alongside it, is a reasonable later contribution and is out of
scope here. It should not be attempted before this library exists,
because the definition worth upstreaming is the one that has been used.

## What is deliberately not here

**Elementary divisors.** The prime-power decomposition of the invariant
factors needs integer factorization, which the project does not have
(see [future-work](../future-work.md)). The invariant factors are
computed without factoring anything, and that is the whole point of the
divisibility chain. When integer factorization arrives, elementary
divisors are a short function on top of `invariantFactors` and belong in
whichever library owns the factorization, not here.

**Smith normal form over `F[x]`.** See "Why `Int` and not a Euclidean
domain class" in [hex-hermite](hex-hermite.md). The polynomial case is
the route to rational canonical form and the minimal polynomial, and it
shares the algorithm shape and none of the normalisation, growth
control, or termination measure.

**Sparse input.** Relation matrices from group presentations are often
very sparse, and dense elimination fills them in immediately. The sparse
matrix item in [future-work](../future-work.md) names this as one of the
cases where a dense representation genuinely fails, and it should be
revisited there rather than worked around here.

## Complexity

`A` is `n × m` with rank `r`. As in [hex-hermite](hex-hermite.md), these
are **matrix-update counts** rather than worst-case complexity, and they
are parameterised by `P`, the number of times the pivot loop repeats at
one diagonal position. `P` is bounded by the bit length of the pivot when
that diagonal stage begins, not by a matrix dimension, since each strict
replacement is by a proper divisor. There is no input-only bound on that
bit length or on the other intermediate operands for this algorithm, which
is the point made under "Algorithms".

| operation | algorithm | matrix updates and `extGcd` calls | operand size |
|---|---|---|---|
| `snf` | form-only classical Euclidean pivot loop | `O(P · r · (n + m) · max n m)` | unbounded; measured, not proved |
| `snfRank`, `invariantFactors` | projections of the form-only run | as `snf` | as `snf` |
| `snfData` | `snf` plus accumulation of `U`, `W`, `V`, and `X` | `+ O(P · r · (n + m) · max n m)` | transforms may exceed the form substantially |
| `snfDiagonal` | form-only normalisation plus fixed adjacent-pair network | `O(r²)` | bounded by the product of the input diagonal |
| `snfDiagonalData` | `snfDiagonal` plus four transform updates | `O(r³)` scalar entry updates in the dense matrices | transform-dependent |
| `abelianStructure` | `snf` plus a filter | as `snf` | as `snf` |

## Conformance

Per [SPEC/testing.md](../testing.md), extending the same shared driver
[hex-hermite](hex-hermite.md) extends: a new `snf` handler in
`scripts/oracle/matrix_flint.py` against FLINT's `fmpz_mat_snf`, an emit
driver `conformance/HexSmith/EmitFixtures.lean` exposed as
`lean_exe hexsmith_emit_fixtures`, a snapshot at
`conformance-fixtures/HexSmith/smith.jsonl`, and one tuple appended to
`ORACLES` in `scripts/ci/run_oracles.sh`:

```
"HexSmith|hexsmith_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexSmith/smith.jsonl"
```

The oracle is compared on the diagonal only, never on `U` or `V`, which
are not unique. The transforms are checked in Lean by the product
identities instead.

**Cases that must be present:**

- the `0 × 0`, `0 × m`, and `n × 0` cases, the zero matrix, and a matrix
  of rank `1`;
- input where the first invariant factor is not the smallest entry, for
  example `[[2, 0], [0, 3]]`, whose Smith normal form is
  `diag(1, 6)`. An implementation that omits the divisibility step in
  the pivot loop returns `diag(2, 3)` here, so this case is the single
  most important one in the suite;
- input whose Smith normal form has a nontrivial chain of length three,
  for example `diag(2, 4, 8)` conjugated by unimodular matrices;
- rank-deficient input, checking the trailing zeros and the rank;
- rectangular input in both orientations;
- negative and mixed-sign entries;
- `[-1]` and a matrix whose final diagonal stage is negative, checking that
  the general pivot loop normalises a pivot even when no elimination step runs;
- a presentation of a known abelian group, checked against
  `abelianStructure`: `[[2, 0], [0, 2]]` gives free rank `0` and torsion
  `#[2, 2]`, while `[[1, 1], [0, 2]]` gives free rank `0` and torsion
  `#[2]`;
- input already in Smith normal form, checking `snf (snf A) = snf A`;
- agreement of `snf`/`snfData` and `snfDiagonal`/`snfDiagonalData` on every
  fixture, plus `snfDiagonal d = snf (diagMatrix d r r)` on every diagonal
  fixture;
- diagonal input through both diagonal paths containing zeros and negatives,
  including `[0, 2]`, `[-2, 0]`, and `[0, 0]`, which is where an
  implementation that skips the normalisation phase divides by zero or
  returns a non-normal form;
- an unsolvable and a solvable integer system checked through
  `solvable_iff_dvd (snfData_isSNF A)`, with `V ≠ I`; the unsolvable case
  has a zero-tail violation so it catches both failure to transform `b` and
  failure to check coordinates after the rank.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), drivers at
`bench/HexSmith/Bench.lean`, no Mathlib import.

**Input families.**

- `random-dense-smith`: uniform entries, square and nonsingular.
- `chain-conjugate`: `U * diag(d) * V` for known `d` with a long
  divisibility chain and random unimodular `U`, `V`, so the expected
  answer is known and the difficulty is entry growth rather than the
  answer's size.
- `presentation-smith`: sparse relation matrices from abelian group
  presentations, the shape the headline consumer produces, run dense.

**Comparators.** FLINT `fmpz_mat_snf` through python-flint,
`informational`. FLINT's default dispatch includes algorithms not
specified here, so the ratio compares different algorithms and does not
hold a required threshold. PARI `matsnf` through `cypari2`, also
`informational`.

**The diagonal decision rule written down in advance.** `snfDiagonal` must
be faster than `snf` on diagonal input by a margin that grows with `r`, since
it skips elimination entirely. A flat or shrinking margin means the fast
path is not being taken, which is a bug rather than a benchmark result. The
report also measures `snfData / snf` and `snfDiagonalData / snfDiagonal`
separately so transform cost is visible rather than charged to form-only
consumers.

**Growth instrumentation is required, not optional.** A separate untimed
diagnostic runner scans the working matrix after each elementary update and
returns peak intermediate entry bit-size. Timed runs use the ordinary
uninstrumented API and report wallclock. The growth curve and wallclock curve,
not an unavailable attribution of time to individual `Int` primitives, are
the evidence for or against specifying Kannan-Bachem.

## File organisation

```
HexSmith/
  Contracts.lean     -- SmithData, AbelianStructure, IsSNF, isSNFShape
  Smith.lean         -- snf, snfRank, snfData, the classical pivot loop
  Diagonal.lean      -- snfDiagonal, snfDiagonalData, fixed gcd/lcm network
  Divisor.lean       -- detDivisor and IsSNF.detDivisor_eq
  Unique.lean        -- IsSNF.rank_eq, IsSNF.diag_eq
  Structure.lean     -- invariantFactors, abelianStructure, solvability and index theorems
  Cert.lean          -- snfCert and its soundness
HexSmith.lean        -- umbrella
HexSmithMathlib/
  Basis.lean         -- Module.Basis.SmithNormalForm from the executable output
  Chain.lean         -- the divisibility chain Mathlib's structure omits
  Quotient.lean      -- the structure theorem for the quotient
HexSmithMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexSmith:
    deps: [HexHermite]
    mathlib: false
    done_through: 0
    status: draft
    phase4:
      comparators:
        - tool: FLINT fmpz_mat_snf via python-flint
          class: informational
          rationale: FLINT dispatches to algorithms and crossover policies outside this SPEC
        - tool: PARI matsnf via cypari2
          class: informational
          rationale: PARI uses a separately tuned implementation and is recorded for orientation
      input_families:
        - name: random-dense-smith
          description: dense square nonsingular integer matrices with uniformly bounded entries
        - name: chain-conjugate
          description: known divisibility chains conjugated by random unimodular matrices
        - name: presentation-smith
          description: sparse abelian-group relation matrices run through the dense implementation
  HexSmithMathlib:
    deps: [HexSmith, HexHermiteMathlib]
    mathlib: true
    done_through: 0
    status: draft
```

Everything else arrives through `HexHermite`.

## Open questions

- **Whether `hex-smith` should be its own library.** The alternative is
  to fold it into `hex-hermite`, which would share the elimination step
  and the certificate module directly rather than through an import.
  The case for two libraries is that the subjects are separable (Hermite
  normal form has consumers that never want Smith normal form), that
  `hex-smith` carries its own Mathlib correspondence, and that the
  project already splits at this granularity (`hex-bareiss` on
  `hex-determinant`, `hex-gfq-field` on `hex-gfq-ring`). Revisit only if
  the shared surface turns out to be larger than the elimination step
  and the certificate.
- **Whether to specify Kannan-Bachem.** The default here is the
  classical pivot loop, which is total and has a termination proof and no
  entry bound. Kannan-Bachem alternates row and column Hermite normal
  forms on trailing submatrices and does have one, at the cost of block
  embeddings, rank-deficient handling, and accumulating the transforms
  through all of it. The growth instrumentation under "Benchmarking" is
  what decides whether that work is called for; it should not be started
  on the strength of the name.
- **Whether to write an Iliopoulos follow-up SPEC.** A public modular path
  needs the complete recurrence, its modulus invariant, a singularity
  theorem for the `Option` boundary, and agreement with `invariantFactors`.
  It is proposed only if the form-only `snf` growth curve shows a production
  range where bounded modular operands are likely to repay that complexity.
- **Whether `detDivisor` should be public at all.** It is the
  specification function and it has no efficient direct evaluation. The
  argument for exporting it is that the statement `d₁ ⋯ d_k = D_k` is
  the thing a mathematician wants to cite; the argument against is that
  a `noncomputable` definition with an exponential unfolding invites
  misuse. It is exported here with its docstring saying so.
- **Sparse relation matrices**, as above. The dense algorithm is
  correct on them and may be far from competitive, and the measurement
  under `presentation-smith` is what decides whether that matters.
