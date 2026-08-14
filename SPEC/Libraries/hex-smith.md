# hex-smith (Smith normal form over `Int`, depends on hex-hermite)

The Smith normal form of an integer matrix: a diagonal matrix `S` with
`S = U * A * V` for unimodular `U` and `V`, whose diagonal entries are
positive and form a divisibility chain `d₁ ∣ d₂ ∣ ⋯ ∣ d_r`. Those
entries are the invariant factors of `A`, and they determine the
structure of the abelian group presented by `A`. Mathlib-free. The
companion `hex-smith-mathlib` builds Mathlib's
`Module.Basis.SmithNormalForm` from the executable output and relates
the invariant factors to the structure theorem for finitely generated
modules over a PID.

This SPEC is the second half of a pair with
[hex-hermite](hex-hermite.md), which fixes the conventions, the
unimodular certificate shape, the entry-growth analysis, and the oracle
this library extends. Read that one first.

## Why this library exists

Hermite normal form answers questions about one lattice. Smith normal
form answers questions about a lattice *inside* another, which is a
different and larger class of question:

- **The structure of a finitely generated abelian group.** Given
  relations as the rows of `A : Matrix Int n m`, the group
  `ℤᵐ / rowlattice A` is `ℤ^(m - r) ⊕ ℤ/d₁ ⊕ ⋯ ⊕ ℤ/d_r`, read directly
  off the diagonal, with the `dᵢ = 1` summands dropped. This is the
  headline consumer and the reason the divisibility chain matters:
  without it the diagonal is not canonical and the summands are not the
  invariant factors.
- **Integer linear systems.** `A x = b` over `ℤ` becomes a diagonal
  system after the change of basis, so solvability is a divisibility
  test per coordinate and the full solution set is a coset of the kernel
  lattice.
- **The index and the order of a quotient.** `[ℤᵐ : rowlattice A]` is
  `∏ dᵢ` when `r = m`, and infinite otherwise.
- **Invariant factors of a module map**, which is what the polynomial
  matrix item in [future-work](../future-work.md) wants over `F[x]`
  rather than `ℤ`. That item is not this library. See "Why `Int`" in
  [hex-hermite](hex-hermite.md).

The dependency on `hex-hermite` is real rather than organisational: the
`extGcd` elimination step with its explicit inverse, the exact-division
discipline, the certificate machinery, the conventions, and the reliance on
`mul_eq_one_comm` are all shared. Note that the default
algorithm below does *not* call `hnf`. The Kannan-Bachem variant under
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

/-- The `n × m` matrix carrying `d` down the leading diagonal. -/
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
ring through the adjugate, by `Hex.Matrix.mul_eq_one_comm` in
`HexDeterminant/Adjugate.lean`. Carrying both
directions as fields would make every construction discharge a
redundant obligation.

**The inverses are data, not existence.** As in the Hermite case, every
elementary step has an explicit inverse, so accumulating `W` and `X`
alongside `U` and `V` costs one extra update per step and removes any
need to invert a matrix afterwards.

**`diagMatrix` should probably move to `hex-matrix`.** It is a general
constructor, `hex-matrix` has no `diagonal` of any kind today, and a
second consumer would immediately want it. It is specified here because
this is the library that needs it first.

## Algorithms

**The default is the classical Euclidean pivot algorithm**, and it is
called that rather than Kannan-Bachem. Kannan-Bachem controls growth by
alternating row and column Hermite normal forms on trailing submatrices,
and its entry bound comes from that repetition. The pivot loop below does
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
4. If some entry `a[i][j]` of the remaining block is not divisible by
   the pivot `p`, add row `i` to the pivot row **and immediately run the
   column-`j` elimination against the new entry**, which replaces `p` by
   `gcd(p, a[i][j])`, then return to step 3. This is the step that
   produces the divisibility chain, and it is the step a naive
   implementation omits.
5. Otherwise advance to the next diagonal position.

**Termination measure.** The pair `(|pivot|, c)` ordered
lexicographically, where `c` is the number of nonzero entries in the
pivot row and column other than the pivot itself. Step 3 either leaves
`|pivot|` fixed and decreases `c` (when the pivot divides the entry, so
the step is a plain subtraction) or strictly decreases `|pivot|` (when
it does not).

Step 4 is why it is stated as one fused step rather than two. Adding row
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

**A modular variant, for the form only.** Iliopoulos's algorithm runs
the elimination modulo a positive multiple of the largest invariant
factor, keeping entries bounded. Two restrictions have to be in the
signature rather than in the prose. It applies to nonsingular square
input, where `hex-bareiss` supplies the modulus. And it computes the
diagonal, not the transforms: the multipliers are not a by-product of the
modular recurrence, and recovering them is a separate algorithm (FLINT
uses an iterated-Hermite routine for the transform case rather than its
modular one). So the entry point is

```lean
/-- The invariant factors of a nonsingular square matrix, computed
modulo a multiple of the largest one. Returns the diagonal only. -/
def snfSquareDiag (A : Matrix Int n n) : Option (Vector Int n)
```

returning `none` on singular input, and it does **not** sit on the
`SmithData` path. Putting it there would mean specifying and proving a
multiplier-reconstruction algorithm, which is not in this SPEC. It is
subject to the same measured decision rule as `hnfSquare` in
[hex-hermite](hex-hermite.md) before it is kept at all.

**A fast path for diagonal input.** A diagonal matrix is already almost
in Smith normal form and needs only normalisation and the chain. The
normalisation is not skippable, because the input diagonal may contain
zeros and negatives: negate the row of each negative entry, move the
nonzero entries stably before the zeros, and take the rank to be the
number of nonzero entries. Every sign change and transposition is
accumulated into all four transform matrices. The gcd and lcm sweep then
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
because `g` divides `b`. Sweeping this over adjacent pairs until no pair
changes yields the chain in `O(r²)` gcd steps. This is FLINT's
`snf_diagonal`, and it is the path a direct-sum presentation of an
abelian group takes, which is the common case for the headline consumer.

**Not specified: Storjohann's algorithms.** The asymptotically fast
methods based on matrix multiplication are out of scope, and the
comparator classification under "Benchmarking" says so rather than
pretending the ratio against FLINT measures the same algorithm.

## API

```lean
namespace Hex.Matrix

/-- Smith normal form data for `A`. -/
def snf (A : Matrix Int n m) : SmithData n m

/-- The invariant factors of `A`, positive and in a divisibility chain. -/
def invariantFactors (A : Matrix Int n m) : Vector Int (snf A).rank

/-- Smith normal form of a diagonal matrix, given its diagonal. -/
def snfDiagonal {r : Nat} (d : Vector Int r) : SmithData r r

/-- The structure of `ℤᵐ / rowlattice A`: the free rank, and the
torsion invariants in a divisibility chain with the units dropped. -/
def abelianStructure (A : Matrix Int n m) : Nat × Array Int

/-- The order of `ℤᵐ / rowlattice A`, or `0` when it is infinite. -/
def quotientOrder (A : Matrix Int n m) : Int

/-- An integer solution of `vecMul x A = b`, or `none` when there is
none. -/
def solveInt (A : Matrix Int n m) (b : Vector Int m) : Option (Vector Int n)

/-- The `k`-th determinantal divisor: the gcd of the determinants of all
`k × k` submatrices of `A`, taken over every choice of `k` rows and `k`
columns. `detDivisor A 0 = 1`, and `detDivisor A k = 0` when
`k > min n m` or when every such minor vanishes.

This is the specification function. Its definition is the gcd above and
mentions nothing about `snf`. `detDivisor_eq_prod` is what says the
invariant factors compute it. -/
noncomputable def detDivisor (A : Matrix Int n m) (k : Nat) : Nat

end Hex.Matrix
```

Contracts to state explicitly. `invariantFactors` drops nothing, so its
leading entries may be `1`. `abelianStructure` drops them, because a
`ℤ/1` summand is not part of anyone's answer, and returns the free rank
`m - rank` separately. `quotientOrder` returns `0` when the free rank is
positive, which is the same convention `latticeIndex` uses in
[hex-hermite](hex-hermite.md) and is a correct value rather than a
fallback.

`solveInt` needs both transforms, not one. From `S = U * A * V`, the
system `vecMul x A = b` becomes `vecMul z S = vecMul b V` with
`z = vecMul x U⁻¹`, so the right-hand side is transformed by `V` before
the diagonal solve, and the answer is mapped back by `x = vecMul z U`.
Solving the diagonal system against `b` directly is wrong whenever
`V ≠ I`, which is the usual case, and the transformed right-hand side
gets its own lemma in the theorem list.

`detDivisor` is `noncomputable` under design principle 11: its definition
enumerates exponentially many minors and there is no runtime twin. It is
**defined by that enumeration and not through `snf`**. Defining it
through `snf` would make `detDivisor_eq_prod` circular, since the
invariant used to prove that `snf`'s output is canonical would already
contain that output. The executable route to its *value* is the product
of the first `k` invariant factors, which is what `detDivisor_eq_prod`
states. It returns `Nat` so that "the gcd" needs no separate
normalisation clause.

## Correctness theorems

```lean
theorem snf_isSNF (A : Matrix Int n m) : IsSNF A (snf A)
theorem snfDiagonal_isSNF {r : Nat} (d : Vector Int r) :
    IsSNF (diagMatrix d r r) (snfDiagonal d)

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

-- Agreement with the Hermite rank, and with the determinant.
theorem IsSNF.rank_eq_hnfRank (h : IsSNF A S) : S.rank = hnfRank A
theorem prod_invariantFactors (A : Matrix Int n n) (h : (snf A).rank = n) :
    (invariantFactors A).foldl (· * ·) 1 = ((det A).natAbs : Int)

-- The consumer-facing statements.
theorem solveInt_iff_diagonal {A : Matrix Int n m} {b} (S := snf A) :
    (∃ x, vecMul x A = b) ↔
      ∃ z, vecMul z (diagMatrix S.diag n m) = vecMul b S.right
theorem solveInt_sound {A : Matrix Int n m} {b x} :
    solveInt A b = some x → vecMul x A = b
theorem solveInt_complete {A : Matrix Int n m} {b} :
    (∃ x, vecMul x A = b) → (solveInt A b).isSome
theorem quotientOrder_eq (A : Matrix Int n m) :
    quotientOrder A =
      if (snf A).rank = m then (invariantFactors A).foldl (· * ·) 1 else 0
```

`IsSNF.detDivisor_eq` is the theorem to prove first, and it must be
stated for every `k` rather than only for `k ≤ S.rank`. The `k ≤ S.rank`
form cannot prove `rank_eq`: if `S.rank < S'.rank`, the value that
separates them is `k = S.rank + 1`, which is exactly where the restricted
statement does not apply. With the all-`k` form, `S.rank` is the largest
`k` whose determinantal divisor is nonzero, which gives `rank_eq`, and
cancelling the positive product of the preceding factors gives
`diag_eq`. Everything the library claims about canonicity rests on it.

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

Smith implementation should not be scheduled before that lands. Nothing
else in this SPEC depends on it, so the executable parts and the
certificate can proceed in parallel with it.

## Certificates

The same shape as [hex-hermite](hex-hermite.md), with one more product:

```lean
/-- Accepts `(S, U, W, V, X, T)` as a Smith normal form of `A`, where
`T = U * A` is the intermediate product. -/
def snfCert (A : Matrix Int n m) (S : SmithData n m) (T : Matrix Int n m) : Bool :=
  Hex.Internal.mulEqCert S.left A T
    && Hex.Internal.mulEqCert S.right.transpose T.transpose
          (diagMatrix S.diag n m).transpose
    && Hex.Internal.mulEqCert S.left S.leftInv (Matrix.identity n)
    && Hex.Internal.mulEqCert S.right S.rightInv (Matrix.identity m)
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
`hex-determinant` prerequisite above. Until that chain is closed, the
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
      (Submodule.span ℤ (Set.range (matrixEquiv A))) (Fin m) (snf A).rank

/-- The divisibility chain, which Mathlib's structure does not carry. -/
theorem smithNormalForm_chain (A : Matrix Int n m) (i : Nat) (h : i + 1 < (snf A).rank) :
    (smithNormalForm A).a ⟨i, by omega⟩ ∣ (smithNormalForm A).a ⟨i + 1, h⟩

/-- The structure theorem, instantiated at the executable output. -/
noncomputable def quotientEquiv (A : Matrix Int n m) :
    (Fin m → ℤ) ⧸ Submodule.span ℤ (Set.range (matrixEquiv A)) ≃ₗ[ℤ]
      (Fin (m - (snf A).rank) → ℤ) × ⨁ i, ℤ ⧸ Ideal.span {invariantFactors A i}
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

**Anything Berlekamp-Zassenhaus needs.** Nothing in the existing tree
depends on this library. Integer factoring of polynomials reaches its
answer without a Smith normal form, so this is new capability rather than
a missing piece of something already built, and it can be scheduled
purely on the strength of its own consumers.

**Sparse input.** Relation matrices from group presentations are often
very sparse, and dense elimination fills them in immediately. The sparse
matrix item in [future-work](../future-work.md) names this as one of the
cases where a dense representation genuinely fails, and it should be
revisited there rather than worked around here.

## Complexity

`A` is `n × m` with rank `r`. As in [hex-hermite](hex-hermite.md), these
are **matrix-update counts** rather than worst-case complexity, and they
are parameterised by `P`, the number of times the pivot loop repeats at
one diagonal position. `P` is bounded by the bit length of the entries,
not by any matrix dimension, since each repetition strictly shrinks the
pivot. There is no proven bound on operand size for this algorithm, which
is the point made under "Algorithms".

| operation | algorithm | matrix updates and `extGcd` calls | operand size |
|---|---|---|---|
| `snf` | classical Euclidean pivot loop | `O(P · r · (n + m) · max n m)` | unbounded; measured, not proved |
| `snfDiagonal` | normalisation plus adjacent-pair sweep | `O(r²)` | bounded by the product of the input diagonal |
| `abelianStructure` | `snf` plus a filter | as `snf` | as `snf` |
| `solveInt` | `snf`, one diagonal solve, two `vecMul`s | `+ O(n · m)` | as `snf` |

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

- the zero matrix, and a matrix of rank `1`;
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
- a presentation of a known abelian group, checked against
  `abelianStructure`: `[[2, 0], [0, 2]]` gives `(0, #[2, 2])` and
  `[[1, 1], [0, 2]]` gives `(0, #[2])`;
- input already in Smith normal form, checking idempotence;
- diagonal input through `snfDiagonal` containing zeros and negatives,
  including `[0, 2]`, `[-2, 0]`, and `[0, 0]`, which is where an
  implementation that skips the normalisation phase divides by zero or
  returns a non-normal form;
- an unsolvable and a solvable integer system through `solveInt`, with
  the solvable one chosen so that `V ≠ I`, which is what catches a
  `solveInt` that forgets to transform the right-hand side.

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

**The decision rules written down in advance.** As in
[hex-hermite](hex-hermite.md), each is stated over a range rather than at
one ladder endpoint.

1. `snfSquareDiag` (modular, form only) is kept only if it wins across
   the upper half of both the dimension and the entry-bit-size ladders on
   `random-dense-smith`, and only if a named consumer wants the diagonal
   without the transforms. It answers a strictly smaller question than
   `snf`, so a win at one point does not justify carrying it.
2. `snfDiagonal` must be faster than `snf` on diagonal input by a margin
   that grows with `r`, since it skips the elimination entirely. A flat
   or shrinking margin means the fast path is not being taken, which is a
   bug rather than a benchmark result. It is not stated as a fixed
   multiple, because at small `r` the two are legitimately comparable.

**Growth instrumentation is required, not optional.** The default
algorithm ships with no proven entry bound, so the bench records peak
intermediate entry bit-size and time spent in big-integer arithmetic
alongside wallclock on every family. Those numbers are the evidence for
or against specifying Kannan-Bachem, per "Open questions".

## File organisation

```
HexSmith/
  Contracts.lean     -- SmithData, diagMatrix, IsSNF, isSNFShape
  Smith.lean         -- snf, the classical Euclidean pivot loop
  Diagonal.lean      -- snfDiagonal: normalisation and the adjacent-pair sweep
  Modular.lean       -- snfSquareDiag, the Iliopoulos variant
  Divisor.lean       -- detDivisor and IsSNF.detDivisor_eq
  Unique.lean        -- IsSNF.rank_eq, IsSNF.diag_eq
  Structure.lean     -- invariantFactors, abelianStructure, quotientOrder, solveInt
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
  what decides whether that work is called for. It should not be started
  on the strength of the name.
- **Whether `detDivisor` should be public at all.** It is the
  specification function and it has no efficient direct evaluation. The
  argument for exporting it is that the statement `d₁ ⋯ d_k = D_k` is
  the thing a mathematician wants to cite. The argument against is that
  a `noncomputable` definition with an exponential unfolding invites
  misuse. It is exported here with its docstring saying so.
- **Sparse relation matrices**, as above. The dense algorithm is
  correct on them and may be far from competitive, and the measurement
  under `presentation-smith` is what decides whether that matters.
