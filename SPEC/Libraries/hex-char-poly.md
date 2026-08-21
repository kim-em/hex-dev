# hex-char-poly (characteristic polynomial, depends on hex-matrix and hex-poly)

The characteristic polynomial `χ_A = det (x·I − A)` of a dense square
matrix, computed by the Samuelson-Berkowitz algorithm. Mathlib-free, and
generic over any commutative ring: the algorithm performs no division and
carries no invertibility side condition. The companion
`hex-char-poly-mathlib` identifies the executable output with Mathlib's
`Matrix.charpoly` and derives Cayley-Hamilton, the trace and determinant
coefficients, and invariance under transpose and similarity from that
identification.

Samuelson-Berkowitz is the algorithm version one ships, and it is the
only one behind the public `charPoly` name. That is a scheduling
statement about this library, not a priority claim against other systems:
FLINT already ships `fmpz_mat_charpoly_berkowitz`, and PARI's `charpoly`
accepts an algorithm flag selecting a division-free method. What is new
here is an executable characteristic polynomial inside the Hex graph with
a proved correspondence to Mathlib's. Mathlib's `Matrix.charpoly` is
`noncomputable`, since `Polynomial R` has no computable representation, so
`(charmatrix M).det` cannot be run.

## Why this library exists

The matrix family holds dense operations in
[hex-matrix](../../HexMatrix/SPEC/hex-matrix.md), rank and nullspace in
hex-row-reduce, the Leibniz determinant and its cofactor theory in
[hex-determinant](../../HexDeterminant/SPEC/hex-determinant.md), and the
fraction-free determinant in hex-bareiss. The characteristic polynomial
is the next invariant of a square matrix, and it answers a class of
question none of those do.

- **Eigenvalues, without ever naming them.** Isolating the roots of
  `χ_A` with hex-real-roots and hex-roots gives certified eigenvalue
  enclosures over `Int`, and hex-number-field names the exact algebraic
  eigenvalues. Neither library needs a new algorithm to do it: they need
  the polynomial.
- **Cayley-Hamilton as a computation.** `χ_A(A) = 0` turns `A^n` into a
  combination of `I, A, …, A^{n-1}`, which is how a consumer computes
  high matrix powers, matrix inverses over a commutative ring, and
  Krylov relations without a linear solve.
- **Two coefficients that are already wanted.** The coefficient of
  `x^{n-1}` is `−tr A` and the constant coefficient is `(−1)^n det A`, so
  the polynomial carries the determinant and the trace and every
  intermediate elementary symmetric function of the eigenvalues in one
  object.
- **The input to the canonical-form work.** The minimal polynomial
  divides `χ_A`, the invariant factors multiply to it, and the rational
  canonical form is read off the invariant factors. Those are separate
  libraries in [future-work](../future-work.md), and each of them wants
  `χ_A` computed independently so its own answer can be compared against
  something that was not derived from it.

## Conventions

`A : Matrix R n n` over a commutative ring `R` with decidable equality.

**The polynomial is `det (x·I − A)`, not `det (A − x·I)`.** The two
differ by `(−1)^n`, and the first is monic for every `n`, which is the
property every downstream statement uses. This choice agrees with
Mathlib's `Matrix.charmatrix`, so the correspondence in the companion is
an equality rather than an equality up to sign.

**Coefficients are stored ascending, and the algorithm produces them
descending.** `Hex.DensePoly` indexes coefficients by exponent: `coeff p
k` is the coefficient of `x^k`. The Berkowitz recursion naturally
produces the vector `(c_n, c_{n-1}, …, c_0)` starting from the leading
coefficient. Rather than restate the recursion backwards, the library
keeps the descending vector as the raw output of `berkowitz` and reverses
once when building the `DensePoly`. The reversal is a named, single step
so that a coefficient-order mistake shows up in one place instead of
being spread through the recursion.

**Degree `n`, including the degenerate cases.** `χ_A` has degree `n`
whenever `(1 : R) ≠ 0`. For `n = 0` it is the constant `1`, which is the
determinant of the empty matrix and matches Mathlib's value. Over the
zero ring `1 = 0`, `DensePoly.ofCoeffs` trims the leading coefficient
away along with everything else and `charPoly A = 0`. Every degree, size,
and coefficient statement below therefore carries `(1 : R) ≠ 0` as a
hypothesis, which is the Mathlib-free analogue of the `[Nontrivial R]`
hypothesis on `Matrix.charpoly_natDegree_eq_dim`.

Monicity is the exception and needs no hypothesis, for the same reason
`Matrix.charpoly_monic` needs none: `Hex.DensePoly.Monic p` unfolds to
`p.leadingCoeff = 1`, and `leadingCoeff (0 : DensePoly R) = 0` by
`Hex.DensePoly.leadingCoeff_zero`, so over the zero ring the equation
`0 = 1` holds and the statement is vacuous rather than false. Do not add
`(1 : R) ≠ 0` to it defensively. It would be an unnecessary hypothesis on
the theorem every downstream division argument uses.

## Why Samuelson-Berkowitz first

The algorithms divide along the line this project cares about, namely
whether they divide at all.

- **Samuelson-Berkowitz** is division-free. It is a total function on
  `Matrix R n n` for every commutative ring `R`, with no pivot condition,
  no invertibility hypothesis, and no failure branch. It costs `O(n⁴)`
  ring operations.
- **Faddeev-LeVerrier** divides by `1, 2, …, n`. It is not merely slower
  in small characteristic, it is inapplicable: over `ZMod p` with
  `p ≤ n`, one of those divisors is `0`, so the recurrence has no value
  to return. A library whose base ring is a parameter cannot offer it as
  a default, and guarding it by `n!` being invertible puts a hypothesis
  in the signature that Berkowitz does not need.
- **Hessenberg reduction** followed by the recurrence on leading
  principal minors, and **Danilevsky's method**, divide by pivot entries.
  Over `Int` each wants a fraction-free reformulation in the style of
  hex-bareiss, or a detour through `Q` and the coefficient growth that
  brings. Both are asymptotically better than `O(n⁴)`, and both are
  partial functions before that reformulation is done.
- **Multi-modular** computes `χ_A` modulo several primes and recombines
  with hex-modular, using a coefficient bound from the matrix norm. The
  determinant in [hex-modular-matrix](hex-modular-matrix.md) is the same
  shape one degree down. It needs a coefficient bound and a modulus
  supply, which are two dependencies version one does not take.

Berkowitz is also the algorithm whose correctness statement is easiest to
get right, because there is nothing to say about when it applies. See
"What is deliberately not here" for the scheduling rule that governs when
any of the others gets specified.

## The algorithm

Fix `A : Matrix R n n`. For `0 ≤ k ≤ n`, write `B_k` for the trailing
`k × k` block of `A`, that is, rows and columns `n − k … n − 1`. So
`B_0` is the empty matrix and `B_n = A`. The recursion computes the
coefficient vector of `χ_{B_k}` from that of `χ_{B_{k-1}}`.

Split `B_{k+1}` as

```text
B_{k+1} = ⎡ a   R ⎤        a : R,  R : Vector R k (a row),
          ⎣ C   B ⎦        C : Vector R k (a column),  B = B_k.
```

Let `T` be the `(k+2) × (k+1)` lower-triangular Toeplitz matrix whose
first column is

```text
t₀ = 1,   t₁ = −a,   t_{j+2} = −(R ⬝ B^j ⬝ C)   for 0 ≤ j ≤ k − 1,
```

so `T[i][l] = t_{i-l}` when `l ≤ i` and `0` otherwise. Then the
descending coefficient vector of `χ_{B_{k+1}}` is `T` applied to the
descending coefficient vector of `χ_{B_k}`, and the recursion starts from
the length-one vector `(1)` for `B_0`.

Worked check at `n = 2`, with `A = [[a, b], [c, d]]`. At `k = 0` the
vector is `(1)`. At `k = 1` the trailing block is `[d]`, the row and
column are empty, and `T = [[1], [−d]]`, giving `(1, −d)`, that is
`x − d`. At `k = 2` we have `a` in the corner, `R = (b)`, `C = (c)`,
`B = [d]`, and `t₀ = 1`, `t₁ = −a`, `t₂ = −bc`, so

```text
⎡  1     0 ⎤              ⎡     1     ⎤
⎢ −a     1 ⎥  ⎡  1 ⎤  =   ⎢  −a − d   ⎥
⎣ −bc   −a ⎦  ⎣ −d ⎦      ⎣ ad − bc   ⎦
```

which is `x² − (a + d) x + (ad − bc)`. The `n = 1` case gives `x − a`,
and `n = 0` gives `1`.

**Which entries these are, and how the vectors are computed.** The step
that produces `χ_{B_{k+1}}` reads from row and column `s = n − k − 1`
onwards: `a = A[s][s]`, `R` is `A[s][s+1 … n-1]`, `C` is
`A[s+1 … n-1][s]`, and `B` is the `k × k` block at offset `(s+1, s+1)`,
which is `(n − k, n − k)`. Materialize `B` once with
`Hex.Matrix.Region.toMatrix` at that offset, read `R` and `C` with
`Vector.ofFn`, then iterate `w₀ = C`, `w_{j+1} = B ⬝ w_j` using
`Hex.Matrix.mulVec`, recording `t_{j+2} = −(R ⬝ w_j)` with
`Hex.Matrix.dotProduct` at each step. Materializing `B` costs `O(k²)` per
step and `O(n³)` overall, which is subdominant to the `O(n⁴)` products,
so the simpler code that calls the existing `mulVec` is the right choice
over reading through a `Region` descriptor inside the inner loop.

**Why the recursion is indexed by block size and not by row index.**
Writing it as "for `i` from `0` to `n − 1`, take the trailing block from
row `i`" forces the vector length to be `n − i + 1`, and every recursive
call then carries a `Nat` subtraction inside a type index. Indexing by
`k`, the size of the trailing block, makes the lengths `k + 1` and
`k + 2` literally, and the only subtraction left is the region offset
`n − k`, which is a `Nat` value with a side condition rather than a type
index. An implementation that ignores this ends up proving length
arithmetic instead of proving the algorithm.

## API

```lean
namespace Hex.Matrix

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R] {n : Nat}

/-- Multiply the `(k+2) × (k+1)` lower-triangular Toeplitz matrix whose
first column is `t` by the vector `v`. -/
def toeplitzMulVec {k : Nat} (t : Vector R (k + 2)) (v : Vector R (k + 1)) :
    Vector R (k + 2)

/-- The Toeplitz first column for the Berkowitz step at trailing block
size `k + 1`: `1`, `−a`, and `−(R ⬝ B^j ⬝ C)` for `0 ≤ j < k`. -/
def berkowitzColumn (A : Matrix R n n) (k : Nat) (hk : k + 1 ≤ n) :
    Vector R (k + 2)

/-- One Berkowitz step: from the descending coefficient vector of the
characteristic polynomial of the trailing `k × k` block of `A` to that of
the trailing `(k+1) × (k+1)` block. -/
def berkowitzStep (A : Matrix R n n) (k : Nat) (hk : k + 1 ≤ n)
    (v : Vector R (k + 1)) : Vector R (k + 2) :=
  toeplitzMulVec (berkowitzColumn A k hk) v

/-- The coefficients of the characteristic polynomial of the trailing
`k × k` block of `A`, in descending degree order. -/
def berkowitzAux (A : Matrix R n n) : (k : Nat) → k ≤ n → Vector R (k + 1)

/-- The coefficients of `χ_A` in **descending** degree order: entry `0`
is the coefficient of `x^n`, entry `n` the constant coefficient. -/
def berkowitz (A : Matrix R n n) : Vector R (n + 1) :=
  berkowitzAux A n (Nat.le_refl n)

/-- The characteristic polynomial `det (x·I − A)`, monic of degree `n`
when `(1 : R) ≠ 0`. -/
def charPoly (A : Matrix R n n) : DensePoly R :=
  DensePoly.ofCoeffs (berkowitz A).reverse.toArray

/-- The sum of the diagonal entries. -/
def trace (A : Matrix R n n) : R

/-- Horner evaluation of a dense polynomial at a square matrix, with the
constant coefficient scaling the identity. -/
def evalMatrix (p : DensePoly R) (A : Matrix R n n) : Matrix R n n

end Hex.Matrix
```

Three placement notes.

**`trace` belongs in hex-matrix, and is specified here because this is
the library that needs it first.** There is no `trace` anywhere in the
current tree. It is a general accessor on a square matrix, it costs one
fold over the diagonal, and a second consumer would want it immediately.
This is the same situation [hex-smith](hex-smith.md) records for
`diagMatrix`, and the two requests should be satisfied by one addition to
hex-matrix rather than by each library growing its own copy. Until that
addition lands, `trace` lives here.

**`evalMatrix` is not a Berkowitz helper.** The algorithm never
evaluates a polynomial at a matrix. `evalMatrix` is here because it is
the operation a consumer needs in order to *use* Cayley-Hamilton, it
needs nothing beyond hex-matrix and hex-poly, and stating
`evalMatrix (charPoly A) A = 0` without it would mean writing the Horner
fold inline in a theorem statement.

**`toeplitzMulVec` is written as the kernel-facing specification.** Its
body folds over all `k + 1` columns with a `l ≤ i` test rather than over
the nonzero range. If that conditional shows up in profiling, the
principle-11 route applies: keep the public name as the specification and
move the range-restricted fold to a `*Impl` twin registered by a proved
`@[csimp]` equality. It is not written that way in advance, because a
`Vector.ofFn` over a fold is already cheap in the kernel and the
speculative split would cost a proof for no measured gain.

## Coefficient and degree properties

These are the statements the Mathlib-free library proves. Each mentions
only hex-matrix and hex-poly.

```lean
theorem berkowitz_zero (A : Matrix R n n) : (berkowitz A)[0] = 1

theorem coeff_charPoly (h1 : (1 : R) ≠ 0) (A : Matrix R n n) {k : Nat} (hk : k ≤ n) :
    (charPoly A).coeff k = (berkowitz A)[n - k]

theorem size_charPoly (h1 : (1 : R) ≠ 0) (A : Matrix R n n) :
    (charPoly A).size = n + 1

theorem degree?_charPoly (h1 : (1 : R) ≠ 0) (A : Matrix R n n) :
    (charPoly A).degree? = some n

theorem charPoly_monic (A : Matrix R n n) : (charPoly A).Monic

theorem coeff_charPoly_pred (h1 : (1 : R) ≠ 0) (A : Matrix R n n) (hn : 0 < n) :
    (charPoly A).coeff (n - 1) = -trace A

theorem charPoly_empty (A : Matrix R 0 0) : charPoly A = 1

theorem charPoly_one_by_one (A : Matrix R 1 1) :
    charPoly A = DensePoly.ofCoeffs #[-A[(0, 0)], 1]

theorem charPoly_two_by_two (A : Matrix R 2 2) :
    charPoly A = DensePoly.ofCoeffs
      #[A[(0, 0)] * A[(1, 1)] - A[(0, 1)] * A[(1, 0)],
        -(A[(0, 0)] + A[(1, 1)]), 1]
```

`berkowitz_zero` is the load-bearing one and it is immediate from the
recursion: `toeplitzMulVec t v` at index `0` is `t₀ * v₀ = 1 * 1`, and
the base case is `#v[1]`. Size and degree follow from it together with
`(1 : R) ≠ 0`, because `DensePoly.ofCoeffs` trims only trailing zeros and
the reversal puts the leading coefficient last. Monicity follows from the
size statement in the nontrivial case and from `leadingCoeff_zero` over
the zero ring, which is the case split its hypothesis-free form costs.

`coeff_charPoly_pred` is the one coefficient identity with a short
Mathlib-free proof. At index `1`, `toeplitzMulVec t v` is
`t₀ * v₁ + t₁ * v₀ = v₁ − a`, so the entry accumulates `−a` once per
step and the induction over `k` gives `−(a_{n-1} + ⋯ + a_0)`. Nothing
else in the coefficient vector telescopes like this, which is why the
determinant coefficient is not on this list.

## What the Mathlib-free layer does not establish

The list above proves that `charPoly A` has the right shape and the right
`x^{n-1}` coefficient. **It does not prove that `charPoly A` is the
characteristic polynomial.** That statement mentions a determinant, and
`Hex.Matrix.det` lives in hex-determinant, which this library does not
depend on. So the identification is a theorem of the companion, and the
Mathlib-free layer says so rather than implying otherwise through a
suggestive theorem name.

This is a deliberate trade and it is worth stating what the alternative
would buy. Depending on hex-determinant would let the library state
`eval (charPoly A) t = det (scalar t − A)` and the principal-minor
characterisation of the coefficients Mathlib-free. It would cost a
dependency that the algorithm itself never calls, since Berkowitz
computes no determinant, and it would make the correctness proof a
Mathlib-free obligation with no Mathlib theorem to transport. The project
already places determinant-level correctness proofs in the companions
(`hex-bareiss-mathlib` proves the Bareiss determinant equals
`Matrix.det`), so putting this one there is the consistent choice rather
than a concession.

**A conformance driver cannot route around this.** The monorepo builds
one `HexConformance` library over the whole tree, so a driver under
`conformance/HexCharPoly/` could import `HexDeterminant` and check
`eval (charPoly A) t` against `det (scalar t − A)` locally. In the split
repos it could not: `scripts/release/released.yml` gives each published
repo one flat `pins` list covering its library, bench, and conformance
sources alike, so a conformance-only import of hex-determinant becomes a
real Lake pin of the released `hex-char-poly`. The determinant
cross-check therefore belongs in the companion or in the external oracle,
and this SPEC puts it in both.

## Verification and certificates

There is no certificate in version one, and the reason is worth writing
down, because the obvious candidate does not work.

**Annihilation is not a certificate.** Checking `p(A) = 0` establishes
that `p` is a multiple of the minimal polynomial of `A` and nothing more.
Adding "monic" and "degree `n`" does not fix it. Take `R = Int`, `n = 2`,
`A = 0`. Then `χ_A = x²`, but `p = x(x − 1) = x² − x` is monic of degree
`2` and satisfies `p(A) = 0` as well, since `A = 0` makes every term with
a positive power of `A` vanish and the constant term of `p` is zero. A
checker that accepts monic degree-`n` annihilators accepts `p` here, and
`p ≠ χ_A`. This case is in the conformance suite for exactly that reason.

**Agreement on the trace and the determinant is a necessary condition
only.** `c_{n-1} = −tr A` and `c_0 = (−1)^n det A` pin down two of the
`n` unknown coefficients, since `c_n = 1` is fixed by monicity. From
`n = 3` upward at least one elementary symmetric function is left
unconstrained by those two checks, so "the trace and the determinant
match" is evidence and not a proof.

**Interpolation is a complete check, and it costs `n` determinants.**
Over an integral domain, if `p` and `χ_A` are both monic of degree `n`,
then `p − χ_A` has degree at most `n − 1`, so it is zero as soon as it
vanishes at `n` distinct points. Evaluating `det (t·I − A)` at `n`
distinct `t` and comparing against `p.eval t` therefore certifies
`p = χ_A` outright, with no second witness needed. The cost is `n`
determinants, which is `O(n⁴)` through hex-bareiss, the same order as
Berkowitz itself, so this is a cross-check rather than a cheap verifier.
It requires an integral domain, it requires `n` distinct elements to
exist in `R`, and it requires a determinant. All three put it outside
this library. It is specified here so that the library that eventually
wants a certified dispatch to an external implementation has the argument
already written down.

## The Mathlib layer

`hex-char-poly-mathlib` depends on hex-char-poly, hex-matrix-mathlib,
hex-poly-mathlib, and hex-determinant-mathlib. The single theorem
everything else comes from:

```lean
namespace HexCharPolyMathlib

open HexMatrixMathlib HexPolyMathlib

variable {R : Type*} [CommRing R] [DecidableEq R] {n : Nat}

/-- The executable characteristic polynomial is Mathlib's. -/
theorem equiv_charPoly (A : Hex.Matrix R n n) :
    HexPolyMathlib.equiv (Hex.Matrix.charPoly A) = Matrix.charpoly (matrixEquiv A)
```

The proof is an induction on the trailing block size, transporting each
Berkowitz step into `Polynomial R` and identifying it with the Laplace
expansion of `det (charmatrix B_{k+1})` along the first row and column.
`hex-determinant-mathlib` is where the determinant identities used in
that step come from, which is why it is a dependency of the companion and
not of the computational library. `Matrix.charmatrix_apply` and
`Matrix.charmatrix_apply_eq` give the entries of the characteristic
matrix, and `HexMatrixMathlib.det_eq` relates any executable determinant
that appears on the way to `Matrix.det`. Note the namespace: that theorem
is declared in `HexDeterminantMathlib/CoreTransport.lean` but sits under
`HexMatrixMathlib`, not under `HexDeterminantMathlib`.

From `equiv_charPoly`, transporting Mathlib's existing results:

```lean
/-- Cayley-Hamilton for the executable objects. -/
theorem evalMatrix_charPoly (A : Hex.Matrix R n n) :
    Hex.Matrix.evalMatrix (Hex.Matrix.charPoly A) A = 0

/-- Horner evaluation at a matrix is Mathlib's `aeval`. -/
theorem equiv_evalMatrix (p : Hex.DensePoly R) (A : Hex.Matrix R n n) :
    matrixEquiv (Hex.Matrix.evalMatrix p A) =
      Polynomial.aeval (matrixEquiv A) (HexPolyMathlib.equiv p)

/-- Evaluating `χ_A` is taking a determinant. -/
theorem eval_charPoly (A : Hex.Matrix R n n) (t : R) :
    (Hex.Matrix.charPoly A).eval t = (Matrix.scalar (Fin n) t - matrixEquiv A).det

/-- The determinant coefficient, which the Mathlib-free layer does not have. -/
theorem coeff_zero_charPoly (A : Hex.Matrix R n n) :
    (Hex.Matrix.charPoly A).coeff 0 = (-1) ^ n * Hex.Matrix.det A

/-- The trace coefficient, agreeing with the Mathlib-free statement. -/
theorem coeff_charPoly_pred (A : Hex.Matrix R n n) (hn : 0 < n) :
    (Hex.Matrix.charPoly A).coeff (n - 1) = -Matrix.trace (matrixEquiv A)

theorem charPoly_transpose (A : Hex.Matrix R n n) :
    Hex.Matrix.charPoly A.transpose = Hex.Matrix.charPoly A

theorem charPoly_conj (A U V : Hex.Matrix R n n) (h : U * V = Hex.Matrix.identity n) :
    Hex.Matrix.charPoly (U * A * V) = Hex.Matrix.charPoly A

end HexCharPolyMathlib
```

`evalMatrix_charPoly` follows from `equiv_evalMatrix`, `equiv_charPoly`,
and `Matrix.aeval_self_charpoly`, which Mathlib proves over an arbitrary
commutative ring. `eval_charPoly` uses `Matrix.eval_charpoly`.
`coeff_zero_charPoly` uses `Matrix.det_eq_sign_charpoly_coeff` together
with `HexMatrixMathlib.det_eq`, and the `n` in the exponent is
`Fintype.card (Fin n)` rewritten. `coeff_charPoly_pred` uses
`Matrix.trace_eq_neg_charpoly_coeff`, whose `[Nonempty n]` hypothesis is
the `0 < n` above. `charPoly_transpose` and `charPoly_conj` are stated
here rather than Mathlib-free because Berkowitz applied to `Aᵀ` is a
different computation from Berkowitz applied to `A`, so there is no
recursion-level argument for either.

**`eval_charPoly` is stated with Mathlib's `Matrix.scalar` on purpose.**
An executable `t·I` would let the identity be stated entirely in terms of
executable objects, which is what a caller wants. hex-matrix has no
diagonal or scalar-matrix constructor today. That gap is already recorded
in [hex-smith](hex-smith.md) under `diagMatrix`, and one constructor in
hex-matrix serves both libraries. If it lands before this one is
implemented, restate `eval_charPoly` against it.

## The Cayley-Hamilton boundary

`evalMatrix (charPoly A) A = 0` is a statement about executable objects
only: `evalMatrix`, `charPoly`, and matrix equality all live in the
Mathlib-free layer. Its *proof* does not, and this section says exactly
what a Mathlib-free proof would need, so that the boundary is a recorded
decision rather than an oversight.

The classical argument multiplies the adjugate identity
`adjugate (x·I − A) * (x·I − A) = det (x·I − A) • I` in
`Matrix (R[x]) n n`, moves it across the isomorphism
`Matrix (R[x]) n n ≃ (Matrix R n n)[x]`, and telescopes. Reproducing it
Mathlib-free needs four things, of which the project has one:

1. **A `Lean.Grind.CommRing (Hex.DensePoly R)` instance.** It does not
   exist. The field lemmas do: `mul_comm_poly`, `mul_assoc_poly`,
   `mul_add_right_poly`, `mul_add_left_poly`, and `mul_one_right_poly` in
   `HexPoly/Euclid/MulRing.lean` are all proved over
   `[Lean.Grind.CommRing S] [DecidableEq S]`, and `HexPoly/Operations.lean`
   supplies the additive and subtraction laws. What is missing is the
   assembled instance. Without it `Matrix (Hex.DensePoly R) n n` has no
   determinant and no adjugate, because both are stated over
   `Lean.Grind.CommRing`. Assembling it is a small, self-contained
   addition to hex-poly and is worth doing on its own merits.
2. **The adjugate identity at `Hex.DensePoly R`.** This one the project
   has: `Hex.Matrix.adjugate_mul` in `HexDeterminant/Adjugate.lean` is
   proved for every `Lean.Grind.CommRing`, so it instantiates as soon as
   item 1 exists.
3. **The analogue of `matPolyEquiv`**, the ring isomorphism between
   matrices of polynomials and polynomials with matrix coefficients,
   plus the telescoping argument over it. The project has nothing of this
   shape and it is not small.
4. **A dependency on hex-determinant**, which items 2 and 3 both force,
   and which this SPEC declines for the reasons under "What the
   Mathlib-free layer does not establish".

So version one proves Cayley-Hamilton in the companion and states it
against the executable objects. Items 1 and 2 are worth revisiting
independently: item 1 unblocks matrices over `Hex.DensePoly R` generally,
which is what the polynomial Smith form item in
[future-work](../future-work.md) needs, and it is the prerequisite for
ever reconsidering item 3.

## Totality and failure-free behaviour

`charPoly` is a total function with no failure mode, and this is a
consequence of the algorithm rather than of a fallback.

- **No division.** Every operation is `+`, `−`, or `*` in `R`. There is
  no exact-division call, no inverse, and no pivot search, so there is
  nothing that can be applied to a zero divisor or to a non-unit.
- **No `Option`, no fallback, no fuel.** The recursion is structural on
  the trailing block size and terminates in `n` steps, so design
  principle 8 does not apply: there is no total form of a partial helper
  anywhere in the library. `berkowitzAux` is defined by cases on `k`
  with the `k ≤ n` hypothesis threaded, and the region offset `n − k` is
  in range by that hypothesis.
- **No side condition on `R`.** Commutativity is used, because the
  Toeplitz recursion needs it. Decidable equality is used only by
  `DensePoly`'s trailing-zero normalisation, not by the algorithm.
  Zero divisors, non-domains, positive characteristic, and
  the zero ring are all admissible inputs. Over the zero ring the answer
  is `0`, which is correct, and the degree statements exclude it by
  hypothesis rather than by a runtime check.
- **Degenerate dimensions.** `n = 0` returns `1` and `n = 1` returns
  `x − a`. Neither is a special case in the code: both fall out of the
  base case and one step.

## Complexity

`A` is `n × n` over `R`, and `H` bounds the absolute value of every entry
when `R = Int`. (`B` is the trailing block in "The algorithm" and is not
reused here.)

| operation | ring multiplications | ring additions | operand bit size when `R = Int` |
|---|---|---|---|
| `berkowitzColumn` at size `k+1` | `k` products of a `k × k` matrix with a vector plus `k` dot products, `k³ + k²` | same order | `O(n log (n H))` |
| `berkowitz` | `n⁴/4 + O(n³)` | same order | `O(n log (n H))` |
| `charPoly` | as `berkowitz` | as `berkowitz` | as `berkowitz` |
| `toeplitzMulVec` at size `k` | `O(k²)`, `O(n³)` summed over the recursion | same order | as `berkowitz` |
| `evalMatrix` of a degree-`d` polynomial | `d` matrix products, `d · n³` | same order | grows with `d` |
| `trace` | `0` | `n − 1` | `log(n H)` |

The `n⁴/4` comes from `Σ_{k<n} k³`. The `O(n³)` Toeplitz products and the
`O(n³)` of block materialization are both subdominant.

**Operand growth is bounded, and the bound is elementary.** Writing `B`
again for the trailing block, entries of `B^j C` are at most `k^j H^{j+1}`
in absolute value, so `|R ⬝ B^j ⬝ C| ≤ k^{j+1} H^{j+2} ≤ n^n H^{n+1}`,
giving `O(n log (n H))` bits. Every partial product `v` in the recursion
is itself the coefficient vector of the characteristic polynomial of a
trailing block, so it obeys the output bound
`|c_{n-k}| ≤ binom(n, k) · k^{k/2} H^k` from Hadamard's inequality
applied to the `k × k` principal minors, which is also `O(n log (n H))`
bits. No intermediate exceeds the output size by more than a constant
factor. This is the concrete respect in which Berkowitz is better behaved
than a fraction-free elimination, whose intermediates are minors of
growing size, and it is why [hex-smith](hex-smith.md)'s warning about
unproven entry growth does not apply here. The benchmark instrumentation
below records the peak intermediate size anyway, because a bound in a
SPEC and a measured curve are different kinds of evidence.

## Conformance

Per [SPEC/testing.md](../testing.md), extending the shared matrix driver
rather than adding a new one: a new `charpoly` handler in
`scripts/oracle/matrix_flint.py` against python-flint's
`fmpz_mat.charpoly()`, an emit driver
`conformance/HexCharPoly/EmitFixtures.lean` exposed as
`lean_exe hexcharpoly_emit_fixtures`, a snapshot at
`conformance-fixtures/HexCharPoly/charpoly.jsonl`, and one tuple appended
to `ORACLES` in `scripts/ci/run_oracles.sh`:

```
"HexCharPoly|hexcharpoly_emit_fixtures|scripts/oracle/matrix_flint.py|conformance-fixtures/HexCharPoly/charpoly.jsonl"
```

The fixture record is the existing `matrix` kind emitted by
`Hex.Conformance.Emit.emitMatrixFixture`, so no new fixture schema is
needed. The result value is the coefficient list.

**The coefficient order in the JSONL is ascending, and the handler must
not normalise it.** FLINT's `fmpz_poly` coefficient list is ascending, so
ascending is also the cheapest thing for the oracle to compare against.
If the emit driver were allowed to send whichever order was convenient, a
reversed implementation would pass on every palindromic case and on every
symmetric-spectrum matrix. Fixing the order in the record and including
an asymmetric case below is what makes a reversal a failure.

**Oracle cases that must be present.** Each is one `matrix` fixture and
one `charpoly` result record, compared against FLINT for exact equality.

- `n = 0` and `n = 1`, checking the constant `1` and `x − a`;
- the zero matrix at `n = 2`, whose answer is `x²`;
- `diag(1, 2, 3)`, whose characteristic polynomial has constant
  coefficient `−6`. Under the `det (A − x·I)` convention the constant
  would be `+6`, so this is the case that catches the sign convention,
  and it must be at odd `n` to do so;
- a nilpotent Jordan block of size `4`, whose answer is `x⁴` and whose
  intermediate `R ⬝ B^j ⬝ C` values are mostly zero, exercising the
  Toeplitz zero-padding;
- an upper-triangular and a lower-triangular matrix, whose answers are
  `∏ (x − a_ii)`;
- a block-triangular matrix whose two diagonal blocks have known and
  different characteristic polynomials, checking the product;
- a matrix and its transpose, as two fixtures, checking that both give
  the same answer;
- a matrix conjugated by an elementary transvection from
  `HexMatrix/Elementary.lean`, whose inverse is the opposite transvection,
  checking similarity invariance without needing a general matrix inverse;
- a matrix with repeated eigenvalues and a non-trivial Jordan structure,
  where the minimal polynomial is a proper divisor of `χ_A`;
- dense random input at `n = 6, 7, 8` with mixed signs, which is where
  a sign error in `t₁` versus `t_{j+2}` shows up;
- input with entries near `2⁶³` at `n = 5`, checking that intermediates
  are arbitrary-precision throughout and that the growth bound above is
  not violated on a case chosen to be adversarial for it.

**Lean-side `#guard` checks**, in `conformance/HexCharPoly/Conformance.lean`,
for the two things the JSONL schema cannot express. The schema has one
`value` per `op`, so neither of these is an oracle record.

- `evalMatrix (charPoly A) A = 0` on every case above. This is a
  necessary condition and not a certificate, per "Verification and
  certificates". It is included because it is cheap and because it
  catches a coefficient-order error that the oracle comparison would
  otherwise be the only check against.
- The negative case for annihilation-only checking, at `n = 2` with
  `A = 0`: both `evalMatrix #p[0, -1, 1] A = 0` and
  `charPoly A ≠ #p[0, -1, 1]`, where `#p[0, -1, 1]` is `x² − x`. The two
  `#guard`s together are the executable statement of the counterexample
  under "Verification and certificates", and they are what stops a later
  implementation from being "verified" by annihilation alone.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), drivers at
`bench/HexCharPoly/Bench.lean`, no Mathlib import.

**Input families.**

- `random-dense-charpoly`: uniform entries over a fixed bit width,
  square, across the dimension ladder. The headline family.
- `small-entry-charpoly`: tridiagonal matrices with entries in
  `{-1, 0, 1, 2}`, following the shape
  `bench/HexDeterminant/Bench.lean` already uses. Big-integer arithmetic
  stays out of the measurement, so the curve tests the `n⁴` operation
  count rather than operand growth.
- `structured-charpoly`: companion matrices and Jordan blocks, whose
  characteristic polynomials are known in closed form, so a wrong answer
  is caught by the bench itself rather than only by conformance.

**Comparators.** FLINT `fmpz_mat_charpoly` through python-flint,
`informational`: FLINT's default entry point dispatches to a modular
algorithm, so the ratio compares different algorithms and does not hold a
required threshold. PARI `charpoly` through `cypari2`, also
`informational`. PARI accepts an algorithm flag that selects a
division-free method, and if the flag available in the PARI version
pinned by `.github/workflows/ci.yml` does select Berkowitz then this is
the one comparator measuring the same algorithm. The benchmarking phase
must confirm the flag against that pinned version before recording the
ratio as a same-algorithm comparison, and must record it as
cross-algorithm otherwise. Both comparators are already installed by the
existing `pip install` step in `ci.yml`, so neither adds a CI dependency.

**No within-Lean comparator in version one.** The natural one is `n`
Bareiss determinants plus interpolation, and it would need hex-bareiss in
the bench sub-project, which becomes a pin of the released repo for the
same reason a conformance import would. It belongs to whichever library
already depends on hex-bareiss.

**Growth instrumentation.** Record peak intermediate coefficient bit size
alongside wallclock on `random-dense-charpoly`. The bound under
"Complexity" predicts that this tracks the output coefficient size to
within a constant factor. A measured curve that does not is either a
refutation of the bound or an implementation that is not the algorithm
specified here, and both need finding.

**Decision rules written down in advance.**

1. Berkowitz remains the public default unless a replacement wins across
   the upper half of both the dimension ladder and the entry-bit-size
   ladder on `random-dense-charpoly`, **and** arrives with a totality
   story that needs no invertibility side condition. A faster partial
   function does not replace a total one, it sits beside it under its own
   name with its own precondition in the signature.
2. A multi-modular implementation is considered only after the growth
   instrumentation shows operand size rather than operation count
   dominating on `random-dense-charpoly`. If the `O(n log (n H))` bound
   holds in measurement, the `n⁴` operation count is the thing to attack
   and multi-modular is the wrong lever.

## What is deliberately not here

**Hessenberg reduction and Danilevsky's method.** Both are faster than
`O(n⁴)` and both divide by pivot entries, so over `Int` each needs a
fraction-free reformulation in the style of hex-bareiss before it is a
total function. They are later alternative implementations behind the
same public `charPoly` name, subject to decision rule 1, and neither is
a dependency of version one.

**Generic Bareiss.** The generic-Bareiss amendment to hex-bareiss in
[future-work](../future-work.md) would let a fraction-free
characteristic-polynomial method be written over an integral domain. That
amendment is not a prerequisite here and this library does not wait on
it. When it lands, the resulting method is evaluated under decision
rule 1 like any other.

**Multi-modular.** As above, and it would add hex-modular and
hex-mod-arith to the dependency set for a coefficient bound and a modulus
supply. [hex-modular-matrix](hex-modular-matrix.md) is the model to
follow when it is specified, including how it discharges the bound in its
companion.

**Eigenvalues.** Root isolation of `χ_A` over `Int` is hex-real-roots and
hex-roots, and naming the exact algebraic eigenvalues is
hex-number-field. All three already exist and all three consume a
polynomial, so nothing here needs to change to serve them. Certified
eigenpair enclosures are a separate item in
[future-work](../future-work.md) with a different method entirely.

**The minimal polynomial.** `hex-min-poly` in
[future-work](../future-work.md) is a separate computation. `χ_A` gives a
useful bound and a cross-check for it, since the minimal polynomial
divides `χ_A`, but it is not an algorithmic prerequisite and this library
does not compute it. Certifying minimality needs a lower-bound witness,
which annihilation plus division into `χ_A` does not supply.

**Invariant factors.** Matrices sharing a characteristic polynomial can
have different invariant factors, so nothing here determines that data.
See the polynomial Smith form and invariant-factor items in
[future-work](../future-work.md).

**Sparse input.** Berkowitz materializes a dense trailing block at every
step, so it is a dense algorithm throughout. Wiedemann's method is the
sparse answer and it is a probabilistic Krylov computation, not a
variant of this one.

## File organisation

```
HexCharPoly/
  Toeplitz.lean     -- toeplitzMulVec and its entry formula
  Berkowitz.lean    -- berkowitzColumn, berkowitzStep, berkowitzAux, berkowitz
  CharPoly.lean     -- charPoly, the coefficient/size/degree/monicity theorems
  Trace.lean        -- trace and coeff_charPoly_pred (until trace moves to hex-matrix)
  EvalMatrix.lean   -- Horner evaluation of a DensePoly at a square matrix
  Small.lean        -- the closed forms at n = 0, 1, 2
HexCharPoly.lean    -- umbrella
HexCharPolyMathlib/
  Basic.lean        -- equiv_charPoly, the correspondence with Matrix.charpoly
  Coeff.lean        -- determinant, trace, degree, monicity transported
  CayleyHamilton.lean -- equiv_evalMatrix and evalMatrix_charPoly
  Invariance.lean   -- charPoly_transpose and charPoly_conj
HexCharPolyMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexCharPoly:
    deps: [HexMatrix, HexPoly]
    mathlib: false
    done_through: 0
    status: draft
  HexCharPolyMathlib:
    deps: [HexCharPoly, HexMatrixMathlib, HexPolyMathlib, HexDeterminantMathlib]
    mathlib: true
    done_through: 0
    status: draft
```

`HexBasic` arrives through `HexMatrix`. The computational dependencies
are two roots of the algebraic graph and nothing else, and neither
`HexMatrix` nor `HexPoly` depends on anything that depends on this
library, so the addition is acyclic. On the Mathlib side,
`HexDeterminantMathlib` depends on `HexDeterminant`, `HexBareiss`, and
`HexMatrixMathlib`, none of which reach `HexCharPoly`, so that addition
is acyclic too.

## Open questions

- **Whether `trace` and a scalar-matrix constructor should land in
  hex-matrix first.** Both are wanted here, `diagMatrix` is wanted by
  [hex-smith](hex-smith.md), and neither exists. One addition to
  hex-matrix satisfies all three requests and removes the temporary
  `Trace.lean` from the file list above. It is not made a prerequisite,
  because the library is implementable without it and the addition is
  independently scheduled.
- **Whether `Lean.Grind.CommRing (Hex.DensePoly R)` should be assembled
  in hex-poly now.** It is not needed by this library, it is needed by
  any Mathlib-free treatment of matrices over polynomials, and the
  component lemmas already exist. The argument for doing it early is that
  it is cheap and it unblocks the Cayley-Hamilton question and the
  polynomial Smith form item. The argument against is that no consumer
  exists yet, so the instance would be an unused public commitment.
- **Whether the descending `berkowitz` vector should be public at all.**
  It is the raw output of the algorithm and it is the natural thing to
  state the recursion theorems about. It is also the one place where a
  caller can pick the wrong coefficient order. The alternative is to keep
  it private and expose only `charPoly`, at the cost of stating every
  recursion lemma about a private definition. It is exported here with a
  docstring that names the order in its first line.
- **Whether a certified dispatch to an external implementation is worth
  building.** The interpolation argument under "Verification and
  certificates" is a complete check, so the shape `hex-lll`'s `certCheck`
  uses would apply. It costs `n` determinants, which is the same
  asymptotic cost as computing the answer, so it only pays if an external
  implementation is a large constant factor faster. The comparator
  measurements are what decide it.
