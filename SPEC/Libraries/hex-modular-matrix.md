# hex-modular-matrix (multi-modular determinant, certified rank, Dixon lifting)

Exact linear algebra over `ℤ` and `ℚ` computed through modular images:
the determinant of an integer matrix from its residues modulo many
moduli, the rank through hex-rank's two-sided certificate produced by a
modular route, and the solution of `A x = b` over `ℚ` by `p`-adic
lifting. Mathlib-free. The companion `hex-modular-matrix-mathlib`
discharges the Hadamard bound the Mathlib-free layer carries as a
hypothesis, and identifies the executable results with `Matrix.det`,
`Matrix.rank`, and `Matrix.mulVec`.

This SPEC depends on the reconstruction operations of
[hex-modular](../../HexModular/SPEC/hex-modular.md) (`Crt`, `crtLoop`,
rational reconstruction) and on the modulus supply in hex-mod-arith
(`ZMod64.Modulus`, `ZMod64.Prime` and `ZMod64.primesBelow` in
`HexModArith/Modulus.lean`). The modular gcd for `ℤ[x]`, the other
consumer of the same machinery, is
[hex-poly-z-gcd](../../HexPolyZGcd/SPEC/hex-poly-z-gcd.md). The rank
certificate is [hex-rank](hex-rank.md)'s, at `R = Int`.

Throughout, `det` is hex-determinant's Leibniz determinant
`Hex.Matrix.det`, the reference every theorem here is stated against.
The total wrappers this library adds (`det`, `detViaDivisor`, `detWith`)
live in `Hex.ModularMatrix`, and the partial operations (`detMod?`, the
bounds, `detBounded?`, `detModular?`) in `Hex.Matrix`, because the plain
`Hex.Matrix.det` and `Hex.Matrix.rank` are hex-determinant's and
hex-rank's. "Public names and dispatch integration" below records the
split.

## Why this library exists

**The gap is measured, and it is a factor of nine.**
[reports/hex-bareiss-performance.md](../../reports/hex-bareiss-performance.md)
records `Hex.Matrix.bareiss` against FLINT's `fmpz_mat.det` on the same
deterministic tridiagonal fixture at twelve rungs from `n = 16` to
`n = 512`. Both arms discard a warmup call, so the ratios are of warmed
medians. The raw ratio crosses unity between `n = 24` and `n = 32` and
falls through every later rung to `0.116x` at `n = 512` (`1.252 s`
against `145 ms`). All twelve rungs are eligible, and the
overhead-adjusted ratio differs from the raw one only at `n = 16` and
`n = 24`, where the subprocess call floor is a visible fraction of the
FLINT time. FLINT spends about a ninth of Hex's wall time on the same
determinant, and the gap widens with `n`.

hex-bareiss's SPEC classifies that comparator as `informational` for a
stated reason: FLINT uses multi-modular reduction with Chinese
remaindering, and Bareiss is fraction-free elimination over `Int`, so the
two have different asymptotic and constant-factor profiles. The report's
own conclusion is that a faster multimodular determinant would be a
distinct surface rather than a repair to Bareiss. This library is that
surface, and implementing it is what turns the comparison into a
like-for-like one.

**Fraction-free elimination pays for coefficient growth it cannot
avoid.** Bareiss keeps every intermediate an integer, and those integers
reach the size of a minor of the input, so an `n³` operation count is an
`n³` count of multiplications on numbers with `O(n log(nB))` bits. A
modular image is `n³` operations on machine words, and the number of
images needed grows only like `n log(nB) / 31`. The trade is one factor
of `n` in the bit complexity, and it is why every computer algebra system
computes integer determinants this way.

**A rational linear solve has no implementation in the tree at all.**
hex-row-reduce solves over a field, so `Matrix Rat n m` works and every
intermediate entry is a rational whose numerator and denominator grow
through the elimination. hex-number-field's arithmetic, the integer
kernel bases in [hex-hermite](../../HexHermite/SPEC/hex-hermite.md), and
the certified rank below all want an exact solve that does not pay that
growth. Dixon lifting is the standard answer and its output is checkable
by one matrix-vector product.

**The modular Hermite route needs a determinant.**
[hex-hermite](../../HexHermite/SPEC/hex-hermite.md) records the
Domich-Kannan-Trotter algorithm as a future SPEC. That algorithm reduces
entries modulo a determinant of a square nonsingular submatrix, and the
only determinant supplier in the tree today is hex-bareiss. The
determinant here is the faster supplier for exactly the sizes where the
modular Hermite route is worth taking.

## What has a checker and what does not

[future-work](../future-work.md) opens with a warning that checking a
positive claim establishes only that claim. Applied to this library, the
three operations come out differently, and the difference drives the
whole design.

**The linear solve has a one-line checker.** A claimed solution `y/d`
is accepted by testing `A y = d b` over `ℤ`, which is one matrix-vector
product. Everything that produced it (the prime, the inverse modulo `p`,
the lifting, the reconstruction) runs untrusted.

**The rank has a two-sided certificate.** [hex-rank](hex-rank.md)
specifies it over any integral domain, and this library produces its
`Int` instance: an `r × r` submatrix `B` of `A`, named by `rows` and
`cols`, with `d = det B` and the adjugate of `B`. The identity
`B * adj = d • identity r` with `d ≠ 0` proves the rank is at least `r`,
and the identity `d • A = A[·, cols] * (adj * A[rows, ·])` proves it is
at most `r`. Both halves are matrix products to check. hex-rank's
`RankCert.det_ne_zero` and `RankCert.det_succ_eq_zero` are the
Mathlib-free theorems, and hex-rank-mathlib's `checkRank_sound` is the
statement against `Matrix.rank`. Everything the modular route does to
find `rows` and `cols` runs untrusted.

**The determinant's witnesses cost as much to check as the answer costs
to compute.** A determinant does have a certificate: a triangular
factorisation `P A = L U` over `ℚ` with `L` unit lower triangular
determines `det A` as `± ∏ᵢ uᵢᵢ`. (An adjugate identity `A * X = d • I`
is not one: it holds with `d = 2` and `X = I` for `A = 2 • I₂`, whose
determinant is `4`, and [hex-rank](hex-rank.md) records the same
counterexample.) Checking the factorisation is an `n × n` product of
big rationals, `O(n³)` multiplications on numbers the size of the
answer, which is the cost of Bareiss itself, so the witness saves the
checker nothing over recomputing. The consequence is not that no certificate exists but that
the multi-modular determinant is a *proved algorithm* rather than a
checked candidate: its correctness theorem is unconditional given a bound
on `|det A|`, that bound is the one analytic input to this library, and
no check runs after the reconstruction. Which reconstruction rules that
permits, and which it forbids, is recorded under "The reconstruction".

That asymmetry has one further consequence worth stating in advance.
Certified dispatch to an untrusted external implementation, in the shape
`hex-lll`'s `certCheck` uses for fpLLL and
[hex-hermite](../../HexHermite/SPEC/hex-hermite.md) specifies for Hermite
forms, is available for the solve and for the rank. For the determinant
it is available only at the price of a Bareiss-sized check, so this SPEC
does not offer it: an external determinant re-verified at the cost of
computing it saves nothing, and an unverified one is what design
principle 4 forbids.

## What the moduli need to be

**Coprime, not prime.** Reduction modulo any `m` is a ring homomorphism,
so `det (A mod m) = (det A) mod m` whether or not `m` is prime, and what
the *elimination* needs is that the pivots it inverts are units, which
the arithmetic discovers rather than assumes. `detMod?` returning `some d`
at a composite modulus is as good an image as any. Distinctness is not
the right property either, since distinct moduli need not be coprime;
coprimality is what the reconstruction needs and `Crt.push` checks it
with one extended gcd.
[hex-modular](../../HexModular/SPEC/hex-modular.md) sets this out in full
under "Primality is not what the checkers need". Primality does appear
here, once: the rank of an image modulo `p` is a rank only when `F_p` is
a field, and the statement of `rankModP` says so.

**The rank's lower bound is a submatrix, not the modular computation.**
Reduction modulo `p` can only lower the rank, but that is not the
evidence. The modular rank is a lower bound because a nonvanishing
`r × r` minor modulo `p` is a nonvanishing integer minor, and hex-rank's
certificate carries the submatrix with its adjugate rather than the
modulus. The modular computation is how the producer finds the
submatrix, and nothing downstream depends on it.

## Scope

In scope: the determinant of a square integer matrix; the rank of a
rectangular integer matrix, as hex-rank's certificate produced by a
modular route; the solution of a square nonsingular integer system over
`ℚ`; a rational kernel basis; and the determinant divisor optimisation
that links the first to the third.

Not in scope for the first version: rectangular and inconsistent systems
(the certificate shape differs and the consistency question is a rank
question); matrix inversion as a returned object, since every consumer
here wants a solve rather than an inverse; the Smith and Hermite normal
forms, which are [hex-smith](../../HexSmith/SPEC/hex-smith.md) and
[hex-hermite](../../HexHermite/SPEC/hex-hermite.md) and want this library
rather than replace it; and the characteristic polynomial, whose
multi-modular form [hex-char-poly](hex-char-poly.md) lists among its
candidate algorithms as a consumer of this determinant.

Coefficients are `Int` throughout. A rational input is cleared to an
integer matrix and a scalar denominator by the caller, and the API says
so rather than accepting `Rat` matrices and doing it silently.

## The determinant

### Public names and dispatch integration

The executable wrappers `det` and `detViaDivisor` below belong in
`Hex.ModularMatrix`, not `Hex.Matrix`: `Hex.Matrix.det` already denotes the
Leibniz reference and cannot be redeclared. Their conditional correctness
lemmas use that wrapper namespace. Mathlib correspondence remains in the
companion namespace. Image, bound, and partial reconstruction operations
remain in `Hex.Matrix`. The shared dispatcher is `Hex.Det.det` in
[hex-det](../../HexDet/SPEC/hex-det.md), above this library.

The total wrappers share this proposed executable interface:

```lean
namespace Hex.ModularMatrix

inductive Method where
  | modular | divisor | bareiss

structure DetData where
  value : Int
  first : Method
  rest : List Method

def detWith (A : Hex.Matrix Int n n) (fuel seed : Nat)
    (useDivisor : Bool) : DetData

end Hex.ModularMatrix
```

`first :: rest` records attempted determinant methods in order. Its last
entry is the method that supplied `value`. With `useDivisor = false`,
`detWith` runs bounded modular reconstruction then Bareiss on exhaustion.
With `useDivisor = true`, it first attempts the seeded divisor optimization,
then ordinary modular reconstruction if the divisor attempt fails, and
finally Bareiss if that reconstruction exhausts its budget. `fuel` bounds
each attempted modular reconstruction and the divisor's bounded search.
At zero fuel no modular or divisor attempt succeeds. Seed affects the
divisor search only. The methods share the algorithm bodies described below.

`det A` projects the value of `detWith A defaultFuel defaultSeed false`.
`detViaDivisor A seed` projects `detWith A defaultFuel seed true`. The
default fuel and seed are recorded implementation parameters. `HexDet`
calls `detWith` with its own recorded parameters, converts this route to its
public route type, and never guesses which fallback ran. Zero-fuel tests
therefore exercise the production branches. The lower library never imports
`HexDet`.

The implementation owes route equations for each success and failure
branch, and `detWith_eq`, asserting that every returned value equals
`Hex.Matrix.det A`. These are proposed obligations, not existing
declarations, and they split across the layers as "The reconstruction"
sets out: the value equations of the `modular` and `divisor` routes are
Mathlib-free under `[Hex.Matrix.LawfulDetBound]`, and `detWith_eq` itself,
whose `bareiss` route needs hex-bareiss-mathlib's determinant equation, is
the companion's. The correctness proofs of `det` and `detViaDivisor`
project this shared result.

### One image

```lean
namespace Hex.Matrix

/-- The determinant of `A` reduced modulo `m`, computed by elimination
below the pivot. Returns `some 0` when a pivot column is entirely zero,
and `none` when the column contains a nonzero entry but no unit, which
for composite `m` can happen without the matrix being singular. -/
def detMod? (A : Matrix (ZMod64 m) n n) : Option (ZMod64 m)
```

**The two failure branches are different and both are needed.** A pivot
column that is entirely zero proves the determinant is zero modulo `m`,
which is a perfectly good residue to fold in: the transformed matrix has
a zero column, so its determinant is `0`, and the accumulated row
operations are determinant-preserving. Only a column with a nonzero
nonunit gives `none`. Collapsing the two makes the determinant of the
zero matrix skip every modulus and never terminate, and it is the kind
of mistake that no oracle fixture catches because the answer is right
whenever the function returns.

A pivot is inverted with `ZMod64.inv?`, the `Option` form of
hex-mod-arith's total `ZMod64.inv` (a prerequisite below). `inv a` is
the Bezout cofactor reduced modulo `m`, which is the inverse exactly
when `a` is a unit, and one multiplication `a * inv a = 1` decides that.
The check runs once per pivot, `n` times per image, and costs nothing
beside the `n³` elimination.

This is a dedicated elimination rather than a call into
`hex-row-reduce`. Three reasons, in order of weight:

- `rowReduce` produces the reduced row echelon form and its transform
  `T` with `T * A = E`. Recovering `det A` from that needs `det T`, which
  `RowEchelonData` does not carry and which is not cheaper to compute
  than the determinant itself.
- Elimination below the pivot is about a third of the work of a full
  Gauss-Jordan reduction, and this is the operation the whole library
  exists to make fast.
- `rowReduce` requires `Lean.Grind.Field`, so it requires the modulus to
  be prime. `detMod?` is written against `inv?` and works at any modulus,
  which is what lets the reconstruction argument drop primality.

Correctness comes from the row-operation determinant lemmas that
hex-determinant already proves: `det_rowSwap`, `det_rowScale`, and
`det_rowAdd` in `HexDeterminant/RowOps.lean`, all stated over any
`Lean.Grind.CommRing`, which `ZMod64 m` is for every `m`. The loop
invariant is that the product of the pivots so far, times the sign of
the accumulated permutation, times the determinant of the untouched
trailing submatrix, equals `det A`.

```lean
theorem detMod?_eq (h : detMod? A = some d) : det A = d
theorem detMod?_reduce (A : Matrix Int n n) :
    detMod? (A.mapEntries (ZMod64.intCast m)) = some d →
      (det A) % (m : Int) = (d.toNat : Int) % (m : Int)
```

The first is the invariant at exit, in the ring `ZMod64 m`. The second is
the reduction homomorphism composed with it: `det` commutes with
`mapEntries` along a ring homomorphism, a lemma about the Leibniz sum
(`det_mapEntries`) that hex-determinant does not have today and
milestone 1 adds beside `mapEntries`. Both hold for every modulus.

### The bound

```lean
/-- The product over rows of the sum of the absolute values of the
entries. An upper bound for `|det A|`, proved here. -/
def rowNormBound (A : Matrix Int n n) : Nat

theorem natAbs_det_le_rowNormBound (A : Matrix Int n n) :
    (det A).natAbs ≤ rowNormBound A

/-- The Hadamard bound: the smaller of the product over columns and
the product over rows of the ceiling of the Euclidean norm. An upper
bound for `|det A|`, never larger than `rowNormBound`, and a hypothesis
in this library. -/
def hadamardBound (A : Matrix Int n n) : Nat

/-- The one analytic fact the default determinant rests on.
Discharged in `hex-modular-matrix-mathlib`. -/
class LawfulDetBound : Prop where
  natAbs_det_le : ∀ {n} (A : Matrix Int n n), (det A).natAbs ≤ hadamardBound A
```

Two bounds, one proved here and one stated here, and the reason for
each.

**The row-norm bound has a Mathlib-free proof, so the library's
correctness does not depend on the companion.** Expand along the first
row (`det_eq_finFoldl_laplace_row` in `HexDeterminant/Laplace.lean`):
`det A = Σⱼ a₀ⱼ · cofactor A 0 j`, and `cofactor` is a sign times the
determinant of `deleteRowCol A 0 j`. With `Int.natAbs_add_le` and
`Int.natAbs_mul` from `Init`, `|det A| ≤ Σⱼ |a₀ⱼ| · |det (deleteRowCol
A 0 j)|`. By induction the minor's determinant is at most the product of
its row sums, and each of those is at most the corresponding row sum of
`A`, because deleting a column drops a nonnegative term. So
`|det A| ≤ (Σⱼ |a₀ⱼ|) · ∏ᵢ≥₁ Σⱼ |aᵢⱼ| = rowNormBound A`. No enumeration
lemma, no analysis, no length of `permutationVectors`. The same bound
also follows from the Leibniz sum by extending it from permutations to
all functions `Fin n → Fin n`, which `columnTupleVectors` in
`HexDeterminant/CauchyBinet.lean` enumerates, but the Laplace induction
is shorter.

**The Hadamard bound is the one the default entry points use, because
the difference is measured in images.** `hadamardBound` is the smaller
of `∏ⱼ ceilSqrt (Σᵢ aᵢⱼ²)` and `∏ᵢ ceilSqrt (Σⱼ aᵢⱼ²)`, two passes over
the matrix and one integer square root per column and per row
(`ceilSqrt` from `HexPolyZ/Mignotte.lean` until it moves). Taking both
forms matters: the column form alone is not comparable with
`rowNormBound` (for `[[N, N], [0, 1]]` it is `N (N + 1)` against `2N`),
while the row form is never larger than `rowNormBound`, because
`Σⱼ aᵢⱼ² ≤ (Σⱼ |aᵢⱼ|)²` and the right side is a perfect square. So
`hadamardBound A ≤ rowNormBound A` always, and a row's `1`-norm exceeds
its `2`-norm by up to `√n`, so the gap is at most `n^{n/2}`. On a dense
matrix with uniform entries of size `B` the gap is about
`(log₂ n)/2 - 0.2` bits per row (`n B / 2` against `√(n/3) · B`): at
`n = 512` about `2200` bits, or `70` moduli of `31` bits, each an
`O(n³)` elimination. Against the Hadamard bound, the Chinese
remaindering of a random dense matrix once the determinant divisor is in
play needs about `0.7 n` bits, a dozen moduli at `n = 512`, so the
row-norm bound would multiply that phase by six or seven. On the
tridiagonal fixture an interior row is `(1, 3, -1)`, with row sum `5`
against `ceilSqrt 11 = 4`, about a third of a bit per row and five or
six extra images at `n = 512`, still several times the count the divisor
leaves. A bound that costs several times the phase it governs is not
the default. Hadamard's inequality is analytic (its proof goes through
Gram-Schmidt), so under design principle 2 the Mathlib-free layer states
it and the companion proves it. The companion has almost nothing to do:
`Matrix.norm_det_le_prod_norm_column` in `HexPolyZMathlib/Hadamard.lean`
is the sharp column form over an `RCLike` field, written for the Mahler
separation bound, and the row form is the same lemma at the transpose
with `det_transpose`. That it lives in a polynomial library is a
placement error, and moving it is one of the relocations below.

**Which theorems carry the hypothesis.** The reconstruction below takes
the bound as a number, so its correctness theorem (`detBounded?_eq`)
carries an explicit inequality `(det A).natAbs ≤ bound` and no instance.
`[LawfulDetBound]` appears on exactly the theorems about the entry
points that choose `hadamardBound`: `detModular?_eq` here, and `det_eq`,
`detWith_eq` and `Decidable (A.det = 0)` in the companion.
`detBounded?_eq`, `natAbs_det_le_rowNormBound`, and therefore
`detBounded? A (rowNormBound A) fuel`, are unconditional in the
Mathlib-free layer. A Mathlib-free consumer that cannot carry the
instance calls `detBounded?` at `rowNormBound` and pays the images. None
exists today. hex-hermite's modular route is the candidate, and this is
the second reason the row-norm bound is a definition rather than a
footnote.

**Why not the Leibniz `n! · Bⁿ` bound.** It needs
`(permutationVectors n).length = n !`, which hex-determinant does not
prove (`HexDeterminant/Enumeration.lean` carries completeness and nodup
lemmas, not a length), and it is not uniformly better than the row-norm
bound. On a matrix all of whose entries are `B` it is smaller by a
factor of about `eⁿ` (`n! · Bⁿ` against `nⁿ · Bⁿ`, `1.44 n` bits), while
on a matrix whose row sums are well under `n · B` (sparse rows, or a few
large entries among small ones) it is larger, since `rowNormBound` reads
the actual row sums and `n! · Bⁿ` reads only the largest entry. Against the Hadamard bound it is worse by
`n log₂ n / 2 - 1.44 n` bits. It is not adopted.

### The reconstruction

```lean
/-- The determinant by Chinese remaindering against a caller-supplied
bound on `|det A|`, or `none` when the supply of moduli runs out before
the accumulated modulus exceeds `2 · bound`. -/
def detBounded? (A : Matrix Int n n) (bound : Nat) (fuel : Nat) : Option Int

/-- `detBounded?` at the Hadamard bound. -/
def detModular? (A : Matrix Int n n) (fuel : Nat) : Option Int :=
  detBounded? A (hadamardBound A) fuel

theorem detBounded?_eq (hB : (det A).natAbs ≤ bound)
    (h : detBounded? A bound fuel = some d) : d = det A
theorem detModular?_eq [LawfulDetBound] (h : detModular? A fuel = some d) :
    d = det A
```

The total wrappers `Hex.ModularMatrix.det` and `detWith` under "Public
names and dispatch integration" project these: with `useDivisor = false`,
`detWith` runs `detModular?` and, on `none`, `Hex.Matrix.bareiss`. There
is no Mathlib-free `det_eq` or `detWith_eq`, and the reason is a boundary
rather than an omission: [hex-bareiss](../../HexBareiss/SPEC/hex-bareiss.md)
places every equation of the form `bareiss M = det M` over the Leibniz
`det` in its companion and forbids restating one in a Mathlib-free
library, so the `bareiss` route of a total theorem cannot be proved
here. The Mathlib-free layer proves the modular route, and the
companion's `det_eq` and `detWith_eq` are the total statements.
[hex-det](../../HexDet/SPEC/hex-det.md) draws the same line for its dispatch: a
Mathlib-free executable is not thereby a Mathlib-free proof.

The loop is hex-modular's `crtLoop` at `k = 1`. `image m` reduces `A`
modulo `m` with `mapEntries`, runs `detMod?`, and returns the residue as
a one-entry vector, or `none` to skip the modulus. `accept` returns the
state's symmetric representative once `2 · bound < state.modulus` and
`none` otherwise. The supply is `ZMod64.primesBelow` from `2^31`
downward: primes are not required (see "What the moduli need to be"),
but among moduli of one size they are the ones every other modulus is
coprime to, so `Crt.push` rejects nothing. The fuel bounds the number of
supply entries inspected.

Correctness is the composition of four facts. `crtLoop_trace` says the
result was accepted on a state reached by folding the consumed moduli
(`CrtTrace`). `push_congr_new` and `push_congr_old` say one push leaves
the state's value congruent to the new image modulo its modulus and to
the old value modulo the old modulus, and `detMod?_reduce` says each
image is `det A` modulo its modulus, so by induction along the trace the
state's value is congruent to `det A` modulo the accumulated product.
The acceptance test gives `2 · |det A| ≤ 2 · bound < modulus`, and the
state carries `2 · |value| ≤ modulus` (`CrtVec.le`), so the class
contains one integer. Two lemmas package this and neither exists yet:
`CrtTrace.congr`, the induction along the trace, and
`CrtVec.eq_of_congr`, the uniqueness with one strict and one non-strict
bound (`crt_unique` is the scalar form with both strict). Both belong in
hex-modular beside `crt_unique` and are listed under the prerequisites.

**The fallback is not defensive coding, it is the only way `det` is
total, and it is the reason the total theorem is the companion's.** `ZMod64.Bounds` caps a modulus at `2^31`, so every allowed
modulus divides `L = lcm(1, …, 2^31 - 1)` and so does every product of
pairwise coprime allowed moduli. On the `1 x 1` matrix `[L]` the
determinant is `L`, every bound is at least `L`, every image is zero, and
the accumulated modulus never exceeds `2L`. No amount of fuel helps.
[hex-modular](../../HexModular/SPEC/hex-modular.md) records the same
obstruction for the supply as a whole. Under design principle 8 the
classification is neither of the two fallback modes: `detBounded?` and
`detModular?` propagate their `Option` upward, and `det` is a dispatch
between two complete algorithms rather than a total form of a partial
one, with the route recorded in `DetData`. The companion's `det_eq` is
therefore two cases, `detModular?_eq` and
`HexMatrixMathlib.bareiss_eq_det` from hex-bareiss-mathlib.

**Early termination is not available here, and this is the one place in
the tree where that has to be said out loud.** Stopping when the
reconstructed value stops changing across two further moduli, and
maximal-quotient reconstruction (`ratReconMaxQuot?`), are what a
consumer with a check may do, and this operation has no check cheaper
than the computation. A determinant produced by a stabilisation rule is
a guess. `detBounded?` therefore stops at the bound and only at the
bound: no implementation of it may return before `2 · bound < modulus`,
and no entry point may pass a bound that is not a proved one. The bound
is not an optimisation to be tuned away. It is the correctness argument.
The next subsection is how to make the bound small rather than how to
avoid it.

### The determinant divisor

The Hadamard bound is pessimistic by a wide margin on almost every input,
and the standard remedy, due to Abbott, Bronstein, and Mulders ("Fast
deterministic computation of determinants of dense matrices", ISSAC
1999), removes the pessimism without weakening the argument.

Build the decomposition of `A` (`decomp?`, in
[Decomposition and repeated solves](#decomposition-and-repeated-solves)),
draw a right-hand side `b`, and solve `A x = b` through it, obtaining
`y` and `d > 0` with `A y = d b` and the pair reduced. Then `d` divides
`det A`, so the remaining factor `det A / d` is bounded by
`hadamardBound A / d`, and Chinese remaindering only has to determine
that much smaller number.

```lean
/-- The divisibility behind the divisor: a reduced solution's
denominator divides the determinant. -/
theorem dvd_det_of_mulVec {A : Matrix Int n n} {y b : Vector Int n} {d : Int}
    (hA : Matrix.det A ≠ 0) (h : A.mulVec y = d • b) (hd : 0 < d)
    (hred : ∀ g : Int, (∀ i : Fin n, g ∣ y[i]) → g ∣ d → g ∣ 1) :
    d ∣ Matrix.det A

/-- The `divisor` route of `Hex.ModularMatrix.detWith`: a divisor found
by lifting times a cofactor found by Chinese remaindering, with the
advanced generator state; `none` when the prime search or the moduli
loop runs out of budget. `fuel` bounds the moduli loop exactly as in
`detModular?`; the prime search uses `solveFuel A`. -/
def detViaDivisorWith (A : Matrix Int n n) (r : Rand) (fuel : Nat) :
    Option Int × Rand

theorem detViaDivisorWith_eq [LawfulDetBound]
    (h : (detViaDivisorWith A r fuel).1 = some d) : d = Matrix.det A
```

This is the algorithm body behind `Hex.ModularMatrix.detWith` at
`useDivisor = true`, and `detViaDivisorWith_eq` is the value equation of
its `divisor` route that "Public names and dispatch integration" asks
for; `Hex.ModularMatrix.detViaDivisor A seed` is that dispatcher's
projection and is not a second definition.

**The right-hand side.** `b` is drawn from `Hex.Rand`
(`HexBasic/Rand.lean`), the splitmix64 generator the tree already has,
under the discipline its module docstring sets: `detViaDivisorWith`
takes the state as an explicit argument and returns the advanced state,
with no monad and no global generator; the dispatcher starts it from
`Rand.ofSeed seed`, so a run is reproducible from its seed; and the draw
affects how many moduli the run needs and never what it returns. Each entry is one `Rand.next` word
truncated to its low sixteen bits and shifted to the symmetric range
`[-2^15, 2^15)`. Truncation of a uniform word to a power of two is
bias-free, so there is no rejection sampling and no `exhausted` branch
to handle. Sixteen bits
is the trade: every bit of `b` is a bit in the numerator bound `P`, hence
a fraction of a lifting digit, and the next paragraph is what the bits
buy.

**What the divisor can be.** Writing `s_n` for the last invariant factor
of `A`, the matrix `s_n · A⁻¹` is integral, so the reduced denominator of
`A⁻¹ b` divides `s_n` for every `b`, and `d = s_n` is the best any
right-hand side can do. The shortfall is `gcd(s_n, c)` for `c` the
relevant integer combination of the entries of `b`, and against an
ideal sampler a prime `q` dividing `s_n` divides `c` with probability
about `1 / q`, so the expected shortfall is a few bits, each of which
costs a fraction of one modulus and never correctness. That is a
statement about cost, made against an ideal sampler as `Hex.Rand`'s
docstring requires, and no theorem depends on it. When `d = s_n` the
cofactor is `det A / s_n = s_1 ⋯ s_{n-1}`, which is `1` exactly when the
cokernel of `A` is cyclic. For a random integer matrix that has density
`∏_{k ≥ 2} ζ(k)⁻¹ ≈ 0.436`, and the cofactor is a few bits with
probability close to `1`; "typical input" below means the dense random
families of the Benchmarking section, on which that heuristic is the
expectation and the measurement is the evidence. The worst case is a unimodular `A`, where `s_n = 1`, every
solution is integral, and the divisor saves nothing; the `unimodular-
determinant` bench family exists to keep that visible. Abbott, Bronstein
and Mulders also combine two right-hand sides by `lcm`, which recovers
the shortfall at the cost of a second lift; it is not adopted for the
first version, and the bench family is where the case for it would be
made.

Three things make this rigorous rather than heuristic, and the middle one
is easy to get wrong:

- `d ∣ det A` is Cramer's rule, and it is Mathlib-free:
  `Hex.Matrix.adjugate_mul` in `HexDeterminant/Adjugate.lean` gives
  `adjugate A * A = det A • identity n`, so from `A y = d b` follows
  `det A • y = d • (adjugate A).mulVec b`, so `d ∣ det A · y_i` for
  every `i`. Then `d / gcd(d, det A)` divides every `y_i` and divides
  `d`, hence divides `1` by reducedness, so `d = gcd(d, det A)` since
  `0 < d`. That is `dvd_det_of_mulVec`, in `Divisor.lean`.
  (`adjugate_mul` is stated at size `n + 1`; the `n = 0` case is
  `det A = 1` and `hred` at `g = d`.)
- **The pair must be reduced first.** The lemma's `hred` is the whole
  hypothesis: without it `d` need not divide `det A`, and the wrong
  answer has no symptom. `ratReconVec?` (`HexModular/Recon.lean`)
  divides its output through by the common gcd, but
  `ratReconVec?_spec` does not say so, and the reconstruction runs
  untrusted. So `solveWith` normalises the pair itself after
  reconstruction and before the check, `solveWith_reduced` states it,
  and `detViaDivisorWith` discharges `hred` from that theorem. The
  route-level test constructs a non-reduced pair and checks the
  normaliser, as the Conformance section says.
- The cofactor still needs a bound, and it has one: `|det A / d| ≤
  hadamardBound A / d`, from `LawfulDetBound` and `d ∣ det A`, with
  floor division on the right. Nothing is assumed about how large `d`
  is. A small `d` costs moduli, never correctness.
- **The images are of the cofactor, not of the determinant**, so each one
  is `(det A mod m) · (d⁻¹ mod m)` and a modulus with `gcd(d, m) ≠ 1` has
  no such inverse. Those moduli are skipped, exactly as the ones where
  `detMod?` returns `none` are. An implementation that reconstructs
  `det A` and divides afterwards has not saved anything, since the point
  of the divisor is to shrink the modulus the reconstruction needs. The
  decomposition's own prime supplies the first image for free: `p ∤ det A`
  and `d ∣ det A` give `p ∤ d`, and `D.detImage · d⁻¹ mod p` needs no
  elimination.

The moduli loop is `crtLoop` (`HexModular/Loop.lean`), the same
combinator `detModular?` uses, with the cofactor image in place of the
determinant image and `2 · (hadamardBound A / d) < modulus` as the
acceptance test, after which `crt_unique` identifies the symmetric
representative with the cofactor and `detViaDivisorWith` returns `d`
times it. `fuel` bounds the supply entries this loop inspects, with the
same meaning as in `detModular?`; the prime search inside `decomp?` has
its own budget, `solveFuel A` from the Dixon section, because the two
loops fail for different reasons and a caller tuning one should not
move the other.

Nonsingularity is not an extra assumption. A matrix invertible modulo
`p` has a determinant that is nonzero modulo `p`, hence nonzero, and
`decomp?` returns `none` when it finds no such prime within its budget,
which on a singular `A` it never does. On the `1 × 1` matrix `[L]` of the totality
argument that is what happens: every prime below `2^31` divides `L`, so
`decomp?` finds nothing and the divisor route never starts.
`detViaDivisorWith` propagates that `none`, and also the `none` of a
moduli loop that runs out of supply before the cofactor is determined,
which the finite supply allows in principle even though a cofactor is
smaller than the determinant it came from. What happens next is the
dispatcher's: `detWith` at `useDivisor = true` continues with
`detModular?` and then `Hex.Matrix.bareiss`, recording the route, and
under design principle 8 each step is a complete algorithm, not a
default value. At zero fuel the moduli loop inspects nothing and the
divisor attempt fails, which is the behaviour the dispatcher's zero-fuel
tests rely on.

This is the entry point a caller should use, and it is what closes the
measured gap: on typical input `d` is within a few bits of the
determinant, so the Chinese remaindering runs over a handful of moduli
instead of hundreds, and the cost becomes the single `O(n³)` inverse plus
the lifting.

## Rank

```lean
/-- The rank of `A` reduced modulo the prime `p`. -/
def rankModP (A : Matrix (ZMod64 p) n m) [ZMod64.PrimeModulus p] : Nat :=
  (rowReduce A).rank

/-- Search for a checked integer rank certificate within the budget. -/
def rankCert? (A : Matrix Int n m) (fuel : Nat) :
    Option (Hex.Matrix.RankCert Int n m)

theorem rankCert?_check (h : rankCert? A fuel = some c) :
    Hex.Matrix.checkRank A c = true

/-- Rank by modular certificate search, with a direct integer fallback. -/
def rankModular (A : Matrix Int n m) : Nat
```

**One certificate and one checker.** The certificate is
`Hex.Matrix.RankCert Int n m` from [hex-rank](hex-rank.md#the-certificate),
with fields `rank`, `rows`, `cols`, `denom`, and `adj`. There is no local
`RankCert` structure or `checkRank` implementation. Write `r := c.rank`,
`d := c.denom`, `B := A[rows, cols] : Matrix Int r r`,
`C := A[·, cols] : Matrix Int n r`, `P := A[rows, ·] : Matrix Int r m`,
and `U := c.adj * P : Matrix Int r m`. `Hex.Matrix.checkRank` checks:

1. `d ≠ 0`;
2. `B * c.adj = d • identity r`;
3. `d • A = C * U`.

There is no modulus field, modular determinant test, or
strictly-increasing check. Distinctness of both index vectors follows
from the nonsingularity forced by identity 2. The checker accepts any
ordering and any common nonzero scaling of `denom` and `adj`; it does
not assert that the fields are the determinant and adjugate. This
producer fills them with `det B` and `adjugate B` in the selected order.

The Mathlib-free lower and upper bounds are hex-rank's
`RankCert.det_ne_zero` and `RankCert.det_succ_eq_zero`, specialised at
`Int`: the selected minor is nonzero and every minor of size `r + 1`
vanishes. No local `ratRank` or duplicate soundness proof is needed.
`HexRankMathlib.checkRank_sound` supplies the `Matrix.rank` statement in
the companion below.

**Producing a certificate.** Each attempt reduces `A` modulo a prime
and calls `Hex.Matrix.rankProfileWith Hex.exactDiv` on that image, using
hex-rank's field exact quotient for `ZMod64 p`. This supplies both the
original row indices and column indices of a nonvanishing `r × r`
minor; its rank is the prime-field rank computed by `rankModP`. The
producer uses this one profile pass, not a separate `rankModP` pass.
`RowEchelonData` from hex-row-reduce supplies pivot columns but no
original-row selection, so it is not used to recover the minor's rows.
The nonzero minor modulo `p` proves the integer minor nonzero, as
explained above. `rankModP` is a rank because its modulus is prime; the
nonzero-residue argument itself needs no primality.

For that square block `B`, use the reusable `Decomp` and repeated-solve
interface specified by [the Dixon and decomposition design](https://github.com/kim-em/hex-dev/issues/10178).
Call its `decompAt? B p` at the already successful prime, then
`solveMatWith` for the `r` right-hand sides; all share one modular
inverse of `B`. Do not call `solve?` independently `r` times or pass the
rectangular block `C` to a square solver. Obtain `d = det B` from
`detModular? B fuel`, falling back to `Hex.Matrix.bareiss B` on `none`.
This deterministic subcall does not use the random determinant-divisor
route. Obtain `adjugate B` by `solveMatWith D (d • identity r)`:
if it returns `(Y, q)`, require exact division of every entry of `Y` by
`q` to obtain `X` with `B * X = d • identity r`. For the exact
determinant these solutions are integral. A failed decomposition, solve,
or inexact division rejects the candidate, and the final
`Hex.Matrix.checkRank A c` is mandatory. The determinant computation is
producer work, never checker work.

Reduced solve denominators alone do not recover `det B`: for
`B = 2 • identity 2`, solving against the unit vectors gives common
denominator `2`, while `det B = 4`. The determinant entry point fixes
this normalisation; neither an lcm of denominators nor its sign is
silently substituted for `det B`. Even an incorrect candidate determinant
cannot make the final rank check unsound, since the checker only needs
the three identities above.

A bad prime can select too small a rank, in which case identity 3 fails
against all the rows and columns of `A` and the search tries another
prime. The modular rank is never too large, by the minor argument.
Reconstruction or resource failure can also reject a candidate; rejection
is not a proof that the modular rank was too small.

**Fuel and failure.** `fuel` bounds the number of prime candidates
examined and the number of moduli tried by each `detModular?` subcall.
`decompAt?` uses the selected prime without another search. The matrix
solve derives a finite digit count from its numerator and denominator
bounds and `p^k > 2 P Q`, as specified by the decomposition interface;
prime-search fuel is not a lifting-digit cap. The determinant subcall
has its total Bareiss fallback. At `fuel = 0`, `rankCert?` returns `none`.
Exhausting the budget or the bounded prime supply returns `none`.
Failed decomposition, reconstruction, inexact division, or a failed
final check rejects an attempt; return `none` if the remaining attempts
are spent without a checked certificate. `none` asserts no rank or
singularity fact.

For `r = 0`, the candidate has empty selections and adjugate and
`denom = 1`; it checks exactly when `A = 0`, including empty shapes.
A nonzero matrix that reduces to zero therefore triggers another prime.
A bounded prime supply need not contain a prime preserving the rank
(the `[lcm(1, …, 2^31 - 1)]` obstruction still applies to the search).
The certificate shape itself is complete: a caller needing a witness
without modular-search failure can use
`Hex.Matrix.rankCertWith HexArith.Int.exactDiv A` from hex-rank.

`rankModular` uses a fixed default budget and returns `c.rank` on
`some c`; on `none` it returns `Hex.Matrix.rank A`, hex-rank's total
fraction-free integer algorithm. “Unchecked” means the caller receives
only a `Nat`, not a certificate; it never means returning the last modular
rank or a guessed zero. `Hex.Matrix.rank` remains hex-rank's entry point,
so these rank entry points can be imported together. Under design
principle 8 this is dispatch to a second complete algorithm, not an
emergency value: `rankCert?` propagates failure, and `rankModular` takes
responsibility for computing the exact answer on that branch.

## The Dixon solve

```lean
/-- Solve `A x = b` over `ℚ` by `p`-adic lifting. Returns the numerator
vector and the common denominator of `x`, reduced as a pair. `fuel` is
the number of primes from the supply tried for an invertible image. -/
def solve? (A : Matrix Int n n) (b : Vector Int n) (fuel : Nat) :
    Option (Vector Int n × Int)

theorem solve?_spec (h : solve? A b fuel = some (y, d)) :
    A.mulVec y = d • b ∧ 0 < d

theorem solve?_reduced (h : solve? A b fuel = some (y, d)) :
    ∀ g : Int, (∀ i : Fin n, g ∣ y[i]) → g ∣ d → g ∣ 1

theorem solve?_unique (h : solve? A b fuel = some (y, d))
    (hA : Matrix.det A ≠ 0) (hz : A.mulVec z = e • b) (he : 0 < e) :
    e • y = d • z
```

`solve? A b fuel` is `decomp? A fuel` followed by `solveWith D b`, both
from the next section, and this section describes what the two do
together. The algorithm, with the two steps that are easy to state
wrongly marked:

1. Find a prime `p` at which `A` is invertible, and compute `B` with
   `B A ≡ I (mod p)`. This is the only `O(n³)` step, and it is done once
   per matrix, not once per right-hand side: it is `decomp?`.
2. Set `r₀ = b`. Repeat: `xᵢ = B rᵢ mod p`, taken as the symmetric
   representative, then `rᵢ₊₁ = (rᵢ - A xᵢ) / p`. **The division is
   exact**, because `A xᵢ ≡ A B rᵢ ≡ rᵢ (mod p)`, and it is a division
   rather than a shift because `p` is not a power of two. It is
   `HexArith.Int.exactDiv` (`HexArith/ExactDiv.lean`), applied
   entrywise; `Hex.Matrix.exactDiv` in hex-bareiss is now an alias of
   it. With symmetric digits the residual satisfies
   `|rᵢ|_∞ ≤ |b|_∞ / pⁱ + (n · B / 2) · p / (p - 1)` for `B` the entry
   bound of `A` and `p > 1`, so it stays uniformly bounded however many
   digits are taken, and each step is
   one `O(n²)` word-arithmetic product and one `O(n²)` product of `A` by
   a digit vector.
3. After `k` steps, `x ≡ Σ xᵢ pⁱ (mod p^k)`, so the solution is known
   modulo `p^k`. This is `Decomp.lift`.
4. Reconstruct with `ratReconVec?` (`HexModular/Recon.lean`) at bounds
   `P = max_i hadamardBound (A with column i replaced by b)` and
   `Q = hadamardBound A`. **The number of steps is set by
   `p^k > 2 P Q`**, from Cramer's rule: the `i`-th numerator is the
   determinant of `A` with column `i` replaced by `b`, and the common
   denominator divides `det A`. The maximum over `i` is not decoration.
   For `A = [[1, N], [0, 1]]` and `b = (0, 1)` the solution is `(-N, 1)`,
   while replacing the second column alone gives a bound of `1`, so a
   `P` read off one replaced column is wrong by a factor of `N`. The
   maximum is `numeratorBound A b`, and it costs `O(n²)` rather than
   `O(n³)`: `hadamardBound` is a product of one factor per column, so
   for `n > 0` and no zero column the maximum over replaced columns is
   `⌈‖b‖⌉ · hadamardBound A / c_min` with `c_min` the smallest column
   factor, and at `n = 0` it is `0`. That is cheap beside the lift,
   which is why the decomposition caches nothing about the bounds. `k`
   is the least power with `p^k > 2 P Q`, found by repeated
   multiplication, which terminates because `1 < p`; there is no
   lifting fuel, because the digit count is determined before the loop
   starts.
5. Divide `y` and `d` through by their common gcd, then check
   `A y = d b` over `ℤ` and return `none` if it fails.

Because of step 5 the whole thing is a checked candidate. `solve?_spec`
and `solve?_reduced` follow from the check and the normalisation alone
and need no hypothesis, not even `LawfulDetBound`: the bound governs how
many lifting steps are enough, which is a question about whether the
check will pass rather than about what it means when it does.

`solve?_unique` is the other half, and the hypothesis it needs is
nonsingularity, which the caller gets for free from step 1: a matrix
invertible modulo `p` has nonzero determinant. The API therefore also
offers

```lean
/-- The solve together with a checkable witness that `A` is nonsingular:
a modulus and the nonzero determinant residue at it. -/
structure SolveWitness (n : Nat) where
  num : Vector Int n
  den : Int
  modulus : Nat
  detImage : Int
  nonzero : detImage ≠ 0

def solveWitness? (A : Matrix Int n n) (b : Vector Int n) (fuel : Nat) :
    Option (SolveWitness n)

theorem solveWitness?_det_ne_zero (h : solveWitness? A b fuel = some w) :
    Matrix.det A ≠ 0
```

The modulus alone witnesses nothing, and an earlier draft of this SPEC
returned only that. What carries the argument is the residue: a nonzero
value of `det A` modulo `w.modulus` proves `det A ≠ 0` as an integer, by
the same one-line argument the rank certificate's lower bound uses. The
solve already computes it, since inverting `A` modulo `p` produces the
pivot product, and the decomposition stores it as `Decomp.detImage`;
`solveWitness?` is `solveWith` with the decomposition's `p` and
`detImage` copied into the result. Primality of the modulus is not part
of the witness and not used by the proof, which is `detMod?_reduce` at
`w.modulus`.

**What `none` means.** There are two ways for `solve?` to return `none`
and they are not the same kind of failure:

- `decomp? A fuel = none`: none of the first `fuel` primes of the supply
  gives an invertible image. This is a resource failure, and it is the
  only failure a caller can observe. The supply `ZMod64.primesBelow`
  (`HexModArith/Modulus.lean`) descends from `2^31`, and while every
  prime tried exceeds `2^30` (the first fifty million or so do), the
  distinct ones dividing a nonzero `det A` multiply to at most
  `|det A| ≤ hadamardBound A`, so at most
  `⌊log₂ (hadamardBound A) / 30⌋` of them are unlucky, and
  `solveFuel A := (hadamardBound A).log2 / 30 + 1` is the default. That
  is `decomp?_isSome` below, and its hypothesis that the primes tried
  all exceed `2^30` is not decoration: the supply is finite, and on the
  `1 × 1` matrix `[L]` of the totality argument every prime below `2^31`
  divides the nonzero determinant, so no budget finds one. So a `none`
  at the default budget is a singular `A` under `LawfulDetBound` whenever
  `hadamardBound A` has fewer than about `1.5 · 10⁹` bits, and is a
  resource failure like `det`'s beyond that; a `none` at a smaller
  budget is not evidence of anything. `solve?` does not certify
  singularity either way; a caller who wants to know why runs
  `rankCert?`.
- `solveWith D b = none`: the check in step 5 failed. On a square input
  with a decomposition this branch is
  `unreachable-by-pipeline-invariant` under design principle 8, with
  `solveWith_isSome [LawfulDetBound]` as the witness theorem: the true
  solution `A⁻¹ b` has reduced common-denominator form within `P` and
  `Q` by Cramer's rule and the bound, `p^k > 2 P Q` makes it the unique
  such pair modulo `p^k`, and `ratReconVec?` finds it by hex-modular's
  completeness theorem. The Mathlib-free layer keeps the check, because
  that is what makes `solve?_spec` hypothesis-free, and states the
  unreachability conditionally.

So for square nonsingular input `none` never means inconsistency, and it
cannot: a square nonsingular system is consistent. There is no digit
budget to exhaust (step 4), and no third outcome. `solve?` does not
return an `Except`, because the only observable failure has one cause.

**Where an inconsistency witness would live.** Rectangular and
inconsistent systems are out of scope, as the Scope section says. When
they are added, the witness `yᵀ A = 0`, `yᵀ b ≠ 0` comes out of the rank
certificate, not out of the lifting: with hex-rank's `RankCert`
(`rows`, `cols`, `denom`, `adj`) the identity
`denom • A = C * (adj * P)` says that every row `i` outside `rows` is
`denom⁻¹ · C[i, ·] · adj` times the rows in `rows`, so
`yᵀ = denom · eᵢᵀ - Σⱼ (C[i, ·] · adj)ⱼ · e_{rows j}ᵀ` annihilates `A`,
and the system is inconsistent exactly when some such `y` has
`yᵀ b ≠ 0`. The rectangular solve is therefore `solveMatWith` on the
`r × r` pivot block against `b[rows]`, checked against every row of `A`,
with a failing row's `y` as the witness; it belongs beside `kernel?` in
`Rank.lean`, which already holds the certificate that produces it. This
SPEC does not specify it.

**Rational input, rational right-hand side.** A caller with `Rat` data
clears denominators. `solve?` does not accept `Rat`, because the
clearing is a scalar multiplication the caller can do exactly once, and
accepting `Rat` would invite it to be done per call.

## Decomposition and repeated solves

Two consumers solve many systems against one matrix. The rank
certificate obtains `adj B` and `det B` from `r` solves against the same
`r × r` block `B`, and a rectangular solve, when it comes, solves
repeatedly against one pivot block. Every solve rebuilding the `O(n³)`
inverse modulo `p` would turn those into `O(n⁴)`. The decomposition is
the object that holds what the lifting reuses.

```lean
/-- A matrix together with what one Dixon lift reuses: a modulus at
which it is invertible, its inverse there, and the determinant residue,
each with the law the lift and the witness need. -/
structure Decomp (n : Nat) where
  A : Matrix Int n n
  p : Nat
  [bounds : ZMod64.Bounds p]
  one_lt : 1 < p
  inv : Matrix (ZMod64 p) n n
  inv_mul : inv * A.mapEntries (ZMod64.intCast p) = Matrix.identity n
  /-- `det A mod p`, as a symmetric representative. -/
  detImage : Int
  detImage_congr : (Matrix.det A - detImage) % (p : Int) = 0
  detImage_lt : 2 * detImage.natAbs < p
  detImage_ne_zero : detImage ≠ 0

/-- `max_i hadamardBound (A with column i replaced by b)`, the numerator
bound Cramer's rule gives a solution of `A x = b`. -/
def numeratorBound (A : Matrix Int n n) (b : Vector Int n) : Nat

/-- The default prime budget: one more than the number of primes above
`2^30` that can divide a determinant within the Hadamard bound. -/
def solveFuel (A : Matrix Int n n) : Nat := (hadamardBound A).log2 / 30 + 1

/-- The decomposition at one modulus, or `none` if `A` is not invertible
there. -/
def decompAt? (A : Matrix Int n n) (p : Nat) [ZMod64.Bounds p] (hp : 1 < p) :
    Option (Decomp n)

/-- The decomposition at the first of `fuel` supply primes at which `A`
is invertible. -/
def decomp? (A : Matrix Int n n) (fuel : Nat) : Option (Decomp n)

/-- The `p`-adic expansion of the solution: `x` with
`A x ≡ b (mod p^k)`, reduced to `0 ≤ x[i] < p^k` after the last digit. -/
def Decomp.lift (D : Decomp n) (b : Vector Int n) (k : Nat) : Vector Int n

/-- One lift, reconstruction, normalisation and check against `D.A`. -/
def solveWith (D : Decomp n) (b : Vector Int n) : Option (Vector Int n × Int)

/-- The same for a matrix right-hand side: `X` and `d` with
`A * X = d • C`, reduced as a whole. -/
def solveMatWith (D : Decomp n) (C : Matrix Int n m) : Option (Matrix Int n m × Int)

def solveMat? (A : Matrix Int n n) (C : Matrix Int n m) (fuel : Nat) :
    Option (Matrix Int n m × Int)

theorem decompAt?_A [ZMod64.Bounds p] (h : decompAt? A p hp = some D) :
    D.A = A ∧ D.p = p
theorem decomp?_A (h : decomp? A fuel = some D) : D.A = A
theorem Decomp.det_ne_zero (D : Decomp n) : Matrix.det D.A ≠ 0
theorem decomp?_isSome [LawfulDetBound] (hA : Matrix.det A ≠ 0)
    (hfuel : (hadamardBound A).log2 / 30 < fuel)
    (hsupply : ∀ q ∈ ZMod64.primesBelow (2 ^ 31 - 1) fuel, 2 ^ 30 < q.m) :
    (decomp? A fuel).isSome
theorem Decomp.lift_spec (D : Decomp n) (b : Vector Int n) (k : Nat) :
    ∀ i : Fin n, ((D.A.mulVec (D.lift b k))[i] - b[i]) % ((D.p : Int) ^ k) = 0
theorem solveWith_spec (h : solveWith D b = some (y, d)) :
    D.A.mulVec y = d • b ∧ 0 < d
theorem solveWith_reduced (h : solveWith D b = some (y, d)) :
    ∀ g : Int, (∀ i : Fin n, g ∣ y[i]) → g ∣ d → g ∣ 1
theorem solveWith_isSome [LawfulDetBound] (D : Decomp n) (b : Vector Int n) :
    (solveWith D b).isSome
theorem solveMatWith_spec (h : solveMatWith D C = some (X, d)) :
    D.A * X = d • C ∧ 0 < d
theorem solveMatWith_reduced (h : solveMatWith D C = some (X, d)) :
    ∀ g : Int, (∀ (i : Fin n) (j : Fin m), g ∣ X[i][j]) → g ∣ d → g ∣ 1
theorem solveMatWith_isSome [LawfulDetBound] (D : Decomp n) (C : Matrix Int n m) :
    (solveMatWith D C).isSome
theorem solveMat?_spec (h : solveMat? A C fuel = some (X, d)) :
    A * X = d • C ∧ 0 < d
theorem solveMat?_unique (h : solveMat? A C fuel = some (X, d))
    (hA : Matrix.det A ≠ 0) (hz : A * Z = e • C) (he : 0 < e) :
    e • X = d • Z
```

**The laws are fields, not comments.** `inv_mul` is what `lift_spec`
uses; `detImage_congr`, `detImage_lt` and `detImage_ne_zero` together
are what `det_ne_zero` uses (a nonzero integer of absolute value below
`p / 2` is nonzero modulo `p`, and `det A` is congruent to it; the
range law is needed, since `detImage ≠ 0` alone does not exclude
`detImage = p`); and `one_lt` is what makes the digit-count search
terminate; so every theorem above holds for every value of the type,
and the producer discharges the fields from the theorems about its own
elimination rather than the consumer trusting the producer. `Bounds p`
alone allows `p = 1`, at which every residue is `0`, the inverse
identity is vacuous and `p^k` never exceeds anything; `one_lt` excludes
it, and `decompAt?` takes the proof so that a caller with a bare
modulus is asked for it once. `decompAt?_A` is stated as two equations
rather than an identity involving `D.inv`, because `D.p` is not
definitionally `p` and a statement mentioning both does not elaborate.

`decompAt?` runs Gauss-Jordan on `[A mod p | identity n]` over `ZMod64 p`
with the `Option`-returning entry inverse, so a pivot column with no unit
gives `none`; it returns the right block and the pivot product, which is
`det A mod p`, lifted to a symmetric representative. Primality is not
used anywhere downstream (the lift needs only `B A ≡ I`, and the witness
needs only a nonzero residue), so `Decomp` carries `ZMod64.Bounds` and
no primality evidence, and `decompAt?` accepts any word-sized modulus.
`decomp?` iterates `decompAt?` over `ZMod64.primesBelow`, because a
composite modulus fails whenever any of its prime factors divides
`det A` and so is never a better choice. A caller that already knows a
good modulus calls `decompAt?` directly: the rank producer found `rows`
and `cols` from a nonvanishing minor modulo its own `p`, so `B` is
invertible there and `decompAt? B p` succeeds without a search.

`solveWith` is steps 2 to 5 of the previous section against `D`, with
`P = numeratorBound D.A b`, `Q = hadamardBound D.A`, and the digit count
`k` from `p^k > 2 P Q`; `solve? A b fuel` is
`(decomp? A fuel).bind (solveWith · b)`, and `solve?_spec`,
`solve?_reduced`, `solve?_unique` are the `solveWith` theorems composed
with `decomp?_A` and `Decomp.det_ne_zero`. At `n = 0` the bounds are
`P = 0` and `Q = 1`, so `k = 0`, and `ratReconVec?` on the empty vector
returns `(#v[], 1)`, which the check accepts: the empty system has the
empty solution with denominator `1`, and nothing special-cases it. `solveWith_isSome` is
`ratReconVec?_complete` (`HexModular/Recon.lean`) applied to the reduced
common-denominator form of `A⁻¹ b`, whose numerators and denominator
are within `P` and `Q` by Cramer's rule under `LawfulDetBound`; the
reducedness that theorem requires is what makes the reduced form the
right pair to name, since at a composite modulus a non-reduced pair
need not be found.

**The matrix form.** `solveMatWith D C` lifts all `m` columns at once:
each digit step is one `ZMod64` matrix product `inv * (Rᵢ mod p)` and one
integer product `A * Xᵢ`, and the reconstruction runs `ratReconVec?` on
the `n · m` residues as one vector, so that the returned `d` is the
common denominator of the whole matrix, and the pair is normalised as a
whole (`solveMatWith_reduced`). The bounds are
`P = max_j numeratorBound A C_j` and `Q = hadamardBound A`: every entry
of `d · A⁻¹ C` is `d / det A` times a replaced-column determinant, and
`d` divides `det A` because the least common denominator of `A⁻¹ C`
does. At `m = 0` or `n = 0` the result is the empty matrix with `d = 1`,
by the same route as the empty vector. Lifting the columns together
rather than in sequence
shares the `p`-adic bookkeeping and turns `m` matrix-vector products per
digit into one matrix product, which is the same work in a better
memory order; the cost is `O(n² m)` word operations per digit, and the
digit count is the one `k` set from the largest column.

**The rank certificate goes through it.** The Rank section's producer
calls `decompAt? B p` at the prime that selected `B`, obtains
`d = det B` from `detModular?`, and calls
`solveMatWith D (d • identity r)`. Because `adjugate B = det B · B⁻¹` is
integral, the reduced pair that returns is `(adjugate B, 1)`
(`solveMatWith_reduced` leaves no common factor, and the check
`B * X = 1 • (d • identity r)` is identity 2 of the certificate), and it
succeeds once `B` has a decomposition (`solveMatWith_isSome`). The
alternative `solveMatWith D (identity r)` returns `(s_r · B⁻¹, s_r)`
with `s_r` the last invariant factor of `B` (the least positive integer
with `s_r · B⁻¹` integral), which for `B = 2 • identity 2` is
`(identity 2, 2)` rather than `(2 • identity 2, 4)`; hex-rank's checker
accepts either, and the Rank section explains why it stores the
determinant and adjugate rather than the reduced pair. At `r = 0` both
return `(identity 0, 1)`. What this section guarantees is the cost: the
`r` solves are one `O(r³)` inverse plus `O(r³ · h / w)` lifting, not `r`
inverses.

**The `p`-adic expansion is exposed, and this settles a question an
earlier draft left open.** A consumer that wants the solution modulo
`p^k` rather than as a rational, a Hensel-style consumer or
[hex-hermite](../../HexHermite/SPEC/hex-hermite.md)'s modular path,
calls `Decomp.lift` directly and skips the reconstruction. `lift_spec`
is its whole contract, the representative is the non-negative one so
that a consumer reducing further can do so by `%`, and the digit count
is the caller's: `lift` does not know the bounds, `solveWith` does. The
decomposition is where the expansion belongs because it is the object
that makes computing it cheap; a `solve?` that returned both would
force every rational consumer to carry a vector it does not want.
[hex-padics](hex-padics.md) records that the residual vector stays an
integer vector rather than a `Vector (ZpApprox p N) n`, and `lift` is
written that way.

## Rational kernel basis

```lean
/-- Integer numerators for a basis of the rational kernel. The rank and
nonzero common denominator come from the checked rank certificate. -/
structure Kernel (n m : Nat) where
  cert : Hex.Matrix.RankCert Int n m
  freeCols : Vector (Fin m) (m - cert.rank)
  basis : Matrix Int m (m - cert.rank)

def kernel? (A : Matrix Int n m) (fuel : Nat) : Option (Kernel n m)
```

Write `K.rank := K.cert.rank` and `K.denom := K.cert.denom` as accessor
abbreviations, not independent fields. The represented rational columns
are `v_j i := (K.basis[i, j] : ℚ) / K.denom`. A raw `Kernel` value
carries data only; the following guarantees require successful `kernel?`.
The numerators and denominator retain the certificate's scaling and are
not reduced by their common gcd.

`kernel?` calls `rankCert?` once and propagates `none`. For a checked
certificate, write `J := c.cols`, and let `F` enumerate the complement of
`J` in increasing original-column order. Distinctness of `J` and
`r ≤ m` follow from the check, so `F` has length `m - r`; no sorting of
`J` or change to the certificate is required. With `P`, `U = c.adj * P`,
and `d` as in the rank section, set `T := U[·, F]`. The integer basis
matrix `N` is given explicitly by

```text
N[J[i], j] = T[i, j]             (i : Fin r)
N[F[k], j] = if k = j then -d else 0.
```

Thus after putting the selected coordinates first, `N = (T, −d I)`
vertically, and the returned rational basis is `(T/d, −I)`. The sets
`J` and `F` partition all coordinates. Restricting identity 3 to `F`
gives `C * T = d • A[·, F]`, hence `A * N = 0` over `Int`.

The executable layer states these Mathlib-free facts:

```lean
theorem kernel?_check (h : kernel? A fuel = some K) :
    Hex.Matrix.checkRank A K.cert = true

theorem kernel?_freeCols (h : kernel? A fuel = some K) :
    K.freeCols.toList =
      (List.finRange m).filter (fun j => decide (j ∉ K.cert.cols.toList))

theorem kernel?_annihilate (h : kernel? A fuel = some K) :
    A * K.basis = Matrix.zero n (m - K.cert.rank)

theorem kernel?_free (h : kernel? A fuel = some K)
    (k j : Fin (m - K.cert.rank)) :
    K.basis[K.freeCols[k], j] = if k = j then -K.cert.denom else 0
```

The pivot entries obey the defining formula `N[J[i], j] = T[i, j]`.
The free-block lemma and `K.cert.denom ≠ 0` imply that `N.mulVec z = 0`
forces `z = 0` over `Int`, and after casting over `ℚ`: read coordinate
`F[k]` to get `-d * z[k] = 0`. This is the full-column-rank argument;
the companion states independence and proves spanning, not just
annihilation. At rank zero the result is `-identity m` with denominator
`1`; at full column rank it has zero columns and the rational kernel is
zero. These include `0 × m` and `n × 0` inputs when fuel is positive.

**Hand check, a `2 × 3` matrix of rank one.** Take

```text
A = [[2, 4, 6], [4, 8, 12]],  rows = [1],  J = [1],  F = [0, 2].
B = [8],  d = 8,  adj = [1],  C = [[4], [8]],  P = [[4, 8, 12]].
U = P,  T = [[4, 12]],  N = [[-8, 0], [4, 12], [0, -8]].
```

Here `B * adj = [8]` and `C * U = [[16, 32, 48], [32, 64, 96]] = 8A`.
The columns of `N/8` are `(-1, 1/2, 0)` and `(0, 3/2, -1)`;
multiplication by either row of `A` gives zero. Their coordinates at
`F = [0, 2]` are `-identity 2`, so they are independent. If
`2x + 4y + 6z = 0`, then `y = -x/2 - 3z/2` and
`(x, y, z) = -x • (-1, 1/2, 0) - z • (0, 3/2, -1)`, proving spanning
explicitly. Using a noninitial selected column checks the reindexing as
well as the signs and denominator.

The integer kernel (a basis of `ker A ∩ ℤ^m` as a lattice, saturated) is
**not** this object, and the difference is the reason
[hex-hermite](hex-hermite.md) exists: `kernelBasis` there is a lattice
basis and this is a vector space basis with a denominator. Both are
wanted, they are not interchangeable, and this SPEC uses the word
"kernel" only for the rational one.

## Complexity

`A` is `n × n` (or `n × m` with rank `r`) with entries bounded by `B`,
moduli of `w = 31` bits, and `H = hadamardBound A`, whose bit length is
`h = (n/2) log₂ n + n log₂ B`.

These are **word-operation counts**. Big-integer operations are counted
separately where they dominate, because that is the whole comparison.

| operation | algorithm | word ops | big-integer ops |
|---|---|---|---|
| `detMod?` | elimination at one modulus | `O(n³)` | none |
| `det` | `⌈h/w⌉` images plus CRT | `O(n³ h / w)` | `O(n · h² / w²)` for the CRT |
| `detViaDivisor` | one decomposition, one solve, `⌈log₂(H/d)/w⌉` images | `O(n³ + n² h / w)` plus `O(n³)` per image | `O(n · h)` in the reconstruction |
| `decomp?` | one Gauss-Jordan inverse modulo `p` per prime tried | `O(n³)` per prime | none |
| `solveWith` | `k = O(h/w)` digit steps against a decomposition | `O(n² h / w)` | `O(n · h)` in the reconstruction |
| `solve?` | `decomp?` plus `solveWith` | `O(n³ + n² h / w)` | `O(n · h)` in the reconstruction |
| `solveMatWith` (`m` columns) | `k = O(h/w)` digit steps, each one matrix product | `O(n² m h / w)` | `O(n m h)` in the reconstruction |
| `rankCert?` | per attempt: modular reduction, `det B`, one decomposition and `r` solves | `O(n m + n m r + r³ + r³ k)` plus the determinant route, for `k` lifting digits per solve | determinant/reconstruction costs plus `checkRank` below |
| `Hex.Matrix.checkRank` | `B * adj`, `adj * P`, `C * U`, and scalar multiplication | none | `O(r³ + r² m + n r m + n m)` ring operations; operand sizes include the certificate |
| `Hex.Matrix.bareiss` | fraction-free elimination | none | `O(n³)` at size up to `h` |

The last two rows are the comparison. Bareiss performs `n³`
multiplications on integers that grow to the size of the answer, so its
bit cost carries a factor of `h` (and, with schoolbook multiplication, of
`h²`). The multi-modular determinant performs `n³ h / w` multiplications
on machine words. Dixon replaces the `h` in the first factor by a single
`O(n³)` inverse plus `O(n²)` per digit, which is where its advantage over
both comes from. The `solveWith` row against the `solve?` row is the
saving of the decomposition: `r` solves against one matrix cost
`O(n³ + r n² h / w)` through it and `O(r n³ + r n² h / w)` without, and
at `r = n` (the rank certificate's `solveMatWith D (identity n)`) the
difference is `n⁴` against `n³`.

## Prerequisite changes in other libraries

Six remain, of which two are shared with other planned libraries and are
listed here because this library is a second consumer. Two earlier ones
are done: `ZMod64.Modulus`, `ZMod64.Prime` and `ZMod64.primesBelow` are in
`HexModArith/Modulus.lean`, and `Hex.Matrix.exactDiv` in hex-bareiss
aliases `HexArith.Int.exactDiv`.

**`ZMod64.inv?` is missing.** hex-mod-arith's `ZMod64.inv` in
`HexModArith/Residue.lean` is total and returns the Bezout cofactor
reduced modulo `m`, which is the inverse exactly when the argument is a
unit. `detMod?` needs the `Option` form, which multiplies once to check
`a * inv a = 1`, together with `inv?_eq_some : inv? a = some b → a * b = 1`.
One definition and one lemma beside `inv`.

**Two CRT lemmas are missing.** `CrtTrace.congr` (a traced state's
value is congruent, modulo the accumulated modulus, to any integer
congruent to every folded image modulo its own modulus) and
`CrtVec.eq_of_congr` (two integers congruent modulo the state's modulus,
one with `2 · |x| < modulus` and the other with `2 · |y| ≤ modulus`, are
equal). Both are the vector forms of arguments hex-modular already makes
for `crt_unique`, and they belong in `HexModular/Loop.lean` and
`HexModular/Crt.lean` beside `crtLoop_trace` and `crt_unique`.

**`zmod64FieldOfPrime` should move to hex-mod-arith.** Set out in
[hex-modular](../../HexModular/SPEC/hex-modular.md). Without it, `rankModP` forces a dependency
on hex-poly-fp for one instance about a `ZMod64` type.

**An entrywise `Matrix.mapEntries` is missing.** hex-matrix has
`mapRows`, `mapRowsIdx`, and `modifyEntries` in `HexMatrix/Basic.lean`,
and no entrywise map. Reducing an integer matrix modulo `m` and lifting a
residue matrix back are the two most-executed operations in this
library, and both are entrywise maps. The function belongs in hex-matrix
next to `mapRows`, with the linear buffer discipline design principle 3
requires, and with the `getElem` characterisation lemma. The companion
lemma `det_mapEntries` (the Leibniz determinant commutes with an
entrywise ring homomorphism) belongs in hex-determinant and is what
`detMod?_reduce` rests on.

**`floorSqrt` and `ceilSqrt` should move to hex-arith**, from
`HexPolyZ/Mignotte.lean` where they still sit under the `Hex.ZPoly`
namespace. `hadamardBound` computes one integer square root per column,
and a Mathlib-free determinant library should not import a polynomial
library for it.

**`exactDiv` has moved to hex-arith.** `HexArith.Int.exactDiv` in
`HexArith/ExactDiv.lean` is the function, and `Hex.Matrix.exactDiv` in
`HexBareiss/Bareiss.lean` is now an alias of it. Dixon's lifting step
divides an exactly-divisible vector by `p` once per digit, which is the
hottest exact division in the tree, and it calls the hex-arith function
directly.

**`ratReconVec?_complete` is in hex-modular.** `HexModular/Recon.lean`
proves that under `2PQ < m` a pair `(y, d)` that is reduced as a whole,
congruent to the residues and within the bounds is what `ratReconVec?`
returns, exactly. The `unreachable-by-pipeline-invariant` classification
of `solveWith`'s check (`solveWith_isSome`) rests on it, and the
reducedness hypothesis is why `solveWith`'s completeness argument
speaks of the reduced form of `A⁻¹ b`: the theorem is false for
non-reduced pairs at composite moduli, as
[hex-modular §Vectors with a common denominator](../../HexModular/SPEC/hex-modular.md)
records with a counterexample.

**The seedable generator already exists.** `Hex.Rand` in
`HexBasic/Rand.lean` (splitmix64, explicit state, `Rand.ofSeed`,
`Rand.next`) is the generator `detViaDivisor` draws from, and the
discipline in its module docstring is the one this SPEC's determinant
divisor section follows. An earlier draft said the tree had none; it
does, and nothing is to be written.

**Hadamard's inequality should move to hex-matrix-mathlib.**
`HexPolyZMathlib/Hadamard.lean` proves
`Matrix.norm_det_le_prod_norm_column` for Mathlib matrices over an
`RCLike` field. It is a determinant inequality with no polynomial content,
`HexRealRootsMathlib/Hadamard.lean` already exists solely as a
compatibility import of it across libraries, and this library's companion
would be a third cross-library consumer. Move the file to
hex-matrix-mathlib and leave compatibility imports in both current
places. Until it moves, the companion imports `HexPolyZMathlib`, and the
`libraries.yml` block below records that dependency.

The rank path imports `HexRank` for its certificate, checker, and total
fallback, and `HexRankMathlib` for soundness and scalar extension. These
are prerequisites for the rank milestone; this library reuses their
implementations and soundness proofs. `Kernel.lean` supplies local
Mathlib-free consequences of a passing check before constructing the
complement: `denom ≠ 0` by projecting the first check, distinct columns
by `RankCert.det_ne_zero` and the repeated-column determinant identity,
and `rank ≤ m` by cardinality of that distinct index vector. These prove
the filtered complement has length `m - rank`; no new hex-rank API is
assumed. The analogous row facts are available by the same argument.

The relocation requests above do not block starting the other milestones.

## Conformance

Fixtures follow [SPEC/testing.md](../testing.md). A Lean driver at
`conformance/HexModularMatrix/EmitFixtures.lean` exposed as
`lean_exe hexmodularmatrix_emit_fixtures`, a committed snapshot at
`conformance-fixtures/HexModularMatrix/modmat.jsonl`, and an oracle
driver at `scripts/oracle/modmat_flint.py`. One tuple appended to
`ORACLES` in `scripts/ci/run_oracles.sh`:

```
"HexModularMatrix|hexmodularmatrix_emit_fixtures|scripts/oracle/modmat_flint.py|conformance-fixtures/HexModularMatrix/modmat.jsonl"
```

python-flint is the oracle: `fmpz_mat.det`, `fmpz_mat.rank`, and
`fmpq_mat.solve` cover all three operations exactly, and the existing
`matrix_flint.py` driver in this repository already speaks the persistent
subprocess protocol, so this extends it rather than adding a second
driver.

**The oracle cannot catch the bugs this library is most likely to
have.** `det` and `detViaDivisor` return the same value, and `rankModular`
falls back to hex-rank's direct integer algorithm, so an end-to-end
fixture passes even if the determinant divisor is never used, the unlucky-prime path
never fires, and the lifting loop silently runs to its fuel limit every
time. The suite therefore has two halves, and the first is worth more.

**Route-level tests**, in Lean, asserting on internals: that
`detViaDivisor` used the number of moduli its divisor allows and not
more; that a modulus at which a pivot is not invertible was skipped
rather than folded in; that `rankCert?` retried after a prime that gave
too small a rank; that the Dixon loop stopped at the predicted digit
count; and that the reduction step in `detViaDivisor` actually reduced a
constructed non-reduced pair.

**Oracle fixtures**, checking the public answers. Cases that must be
present:

- `n = 0` and `n = 1`, where the determinant conventions live.
- A singular matrix, a matrix singular modulo the first few primes but
  not over `ℤ` (take a matrix whose determinant is a product of small
  primes), and a matrix whose determinant is exactly a modulus.
- A determinant near the Hadamard bound (a Hadamard matrix scaled) and
  one enormously below it with a large divisor: a matrix of large entries
  whose determinant is a small non-unit, say `6`, where the solve's
  denominator carries almost all of the answer. **Not** a unit-diagonal
  triangular matrix, which is unimodular, so every rational solution has
  denominator `1` and the divisor is `1`. That is the divisor method's
  worst case rather than its best, and using it as the demonstration
  contradicts the family list below.
- A determinant of `±1`, where the divisor is `1` and no shortcut helps.
- A **composite** modulus at which the elimination succeeds, for instance
  a matrix with determinant `5` reduced modulo `6`, which is the case the
  no-primality claim rests on and which a suite of prime moduli never
  reaches.
- A matrix whose pivot column modulo a composite modulus is nonzero with
  no unit, so `detMod?` returns `none`, beside one whose pivot column is
  entirely zero, so it returns `some 0`. These are the two branches that
  an oracle comparison cannot distinguish.
- The `1 x 1` matrix `[L]` from the totality argument is not a fixture:
  `L` has hundreds of millions of digits. The Bareiss fallback is
  exercised instead by a fuel of zero, which is the same code path.
- `detBounded?` at `rowNormBound` beside `detModular?` on the same
  inputs, so the unconditional route is exercised and its image count
  recorded next to the Hadamard one.
- Rank cases: full rank, rank zero, rank deficient by one, wide and tall,
  and a matrix whose rank drops modulo a small prime, constructed so the
  certificate producer must retry.
- Solve cases: a system whose solution has a large denominator, one whose
  solution is integral, and one where the numerators are much larger than
  the denominator.
- A matrix with entries of several thousand bits, where the word-op count
  and the big-integer count separate.
- Sign conventions on the determinant against FLINT, since the report
  records that Bareiss tracks the swap permutation parity and FLINT's
  multimodular path returns the same value by a different route.

## Benchmarking

Per [SPEC/benchmarking.md](../benchmarking.md), with drivers at
`bench/HexModularMatrix/Bench.lean`. Native only. There is no kernel
suite: the kernel-facing operation here is `checkRank`, whose cost is a
matrix product hex-matrix already measures.

Families:

- **Structured determinant**, the same deterministic tridiagonal fixture
  `bench/HexBareiss/Bench.lean` uses, at the same twelve rungs
  `n = 16 … 512`, for both `det` and `detViaDivisor`. Using the
  identical fixture is the point: it makes the new path directly
  comparable both to `Hex.Matrix.bareiss` and to the FLINT numbers
  already recorded in
  [reports/hex-bareiss-performance.md](../../reports/hex-bareiss-performance.md).
- **Dense random determinant**, entries of 8, 64, and 1024 bits, at
  `n = 32 … 256`. The entry-size sweep is where the multi-modular
  advantage should grow, since the number of moduli grows with the entry
  size while Bareiss's operand size grows with both.
- **Unimodular determinant**, matrices with determinant `±1`, which is
  the worst case for the determinant divisor and the family that keeps
  the headline number honest.
- **Rank**, square and rectangular, at several ranks including full and
  nearly full, measuring `rankCert?` and the public `rankModular` path.
  Include a `rank-bad-primes` family with large coefficients: for
  `0 < r < min n m`, use `A = s L R`, where the first `r` rows of
  `L : Matrix Int n r` and first `r` columns of `R : Matrix Int r m`
  are identities, their other entries are large, and `s` is the product
  of the first few primes in the producer's actual supply. The rank is
  exactly `r`, drops to zero at those primes, and is `r` at the next
  prime. The driver constructs `s` from the supply used by that run and
  asserts the expected initial skips and success at the next prime, so a
  supply change cannot silently stop exercising the route. Record
  rejected primes, successful certificates and fallback use; size the
  budget to require successful recovery after the skips.
  Keep forced fuel-exhaustion cases separately labelled so that a fast
  fallback cannot stand in for modular-rank performance. The rank
  comparator is `FLINT fmpz_mat_rank via python-flint`, `informational`
  because there is no shared fixture history and crossover policies
  differ. Also measure `Hex.Matrix.rank` on the same inputs to record
  the crossover with the direct algorithm: the mandatory certificate
  check still costs big-integer products. The initial dispatch is on
  failure only; a size threshold requires these measurements.
- **Solve**, single right-hand sides with integral solutions and with
  large-denominator solutions, at `n = 32 … 256`, timing `decomp?` and
  `solveWith` separately so the inverse and the lifting are attributed.
- **Repeated solve**, `r` right-hand sides against one matrix at
  `r = 1, 8, n`, once through one decomposition (`solveMatWith`) and once
  as `r` independent `solve?` calls. The difference is the `(r - 1)`
  inverses the decomposition saves, and at `r = n` it is the cost of the
  rank certificate's adjugate. FLINT has no counterpart for this family,
  since `fmpq_mat_solve` does not expose its decomposition.

**Comparators.** FLINT's `fmpz_mat_det` carries `class: gating` here,
the required-check classification of
[SPEC/benchmarking.md](../benchmarking.md), and this is the one
classification change this SPEC makes to an existing
comparator relationship. hex-bareiss classifies it `informational`
because the algorithms differ; once this library implements the same
algorithm the comparison is like-for-like and the reason for the
exemption is gone. Two thresholds, written against the numbers in
[reports/hex-bareiss-performance.md](../../reports/hex-bareiss-performance.md)
as they stand:

- **Against `Hex.Matrix.bareiss`**, on the shared tridiagonal fixture in
  the same run, `detViaDivisor` must be faster at `n = 512` by at least
  `4x`. On the report's host that is `313 ms` against Bareiss's
  `1.252 s`, which is `2.2x` FLINT's `145 ms`. The crossover rung below
  which Bareiss wins is **measured rather than predicted**, then written
  into the dispatch and into this SPEC. An earlier draft required "faster
  at every rung `n ≥ 64`", which guesses the crossover in the same
  document that says it will not guess it.
- **Against FLINT `fmpz_mat.det`**, on the same fixture and using the
  same warmed, overhead-adjusted ratio the report defines,
  `detViaDivisor` should be within `5x` at every eligible rung. At
  `n = 512` the Bareiss threshold already implies `2.2x`, so the `5x`
  target binds only at the small rungs, where the modular route pays its
  fixed costs against a FLINT time of tens of microseconds. `5x` is a
  plausible constant factor between Lean and tuned C over GMP once the
  algorithms agree, and it is a target rather than a proved-reachable
  number: it becomes the required threshold after the first
  implementation measures it, and until then a miss is a finding to
  investigate rather than a merge-blocking failure.

Stating it that way is deliberate. A required check whose number nobody
has measured is either vacuous or an accident waiting to block a correct
implementation, and this SPEC has no prototype behind the FLINT figure.
Absolute times are host-specific observations. The thresholds are
ratios within one run.

FLINT's `fmpz_mat.rank` and `fmpq_mat.solve` are `informational`: FLINT's
solve uses a tuned multi-modular and Dixon hybrid with a different
crossover policy, and there is no shared fixture history to anchor a
required ratio.

## The Mathlib layer

`hex-modular-matrix-mathlib` discharges the hypothesis and transports the
results. Writing `e` for hex-matrix-mathlib's `matrixEquiv`, the rank
statements below use `A : Hex.Matrix Int n m`,
`c : Hex.Matrix.RankCert Int n m`, and `K : Kernel n m`. For the kernel
statements abbreviate `M := (e A).map (Int.castRingHom ℚ)` and
`v j i := (K.basis[i, j] : ℚ) / (K.cert.denom : ℚ)`:

```lean
instance : LawfulDetBound        -- from Matrix.norm_det_le_prod_norm_column

theorem det_eq (A : Hex.Matrix Int n n) :
    Hex.ModularMatrix.det A = Matrix.det (e A)
theorem rank_eq (h : Hex.Matrix.checkRank A c = true) :
    (e A).rank = c.rank := HexRankMathlib.checkRank_sound h

theorem rankModular_eq (A : Hex.Matrix Int n m) :
    rankModular A = (e A).rank

theorem solve_eq (h : solve? A b fuel = some (y, d)) :
    Matrix.mulVec ((e A).map (Int.cast : ℤ → ℚ)) (fun i => ((y[i] : ℤ) : ℚ) / d) =
      fun i => ((b[i] : ℤ) : ℚ)
theorem solve_eq_inv (h : solve? A b fuel = some (y, d)) :
    (fun i => ((y[i] : ℤ) : ℚ) / d) =
      ((e A).map (Int.cast : ℤ → ℚ))⁻¹.mulVec (fun i => ((b[i] : ℤ) : ℚ))
theorem solveMat_eq (h : solveMat? A C fuel = some (X, d)) :
    (e A).map (Int.cast : ℤ → ℚ) * (e X).map (fun x => (x : ℚ) / d) =
      (e C).map (Int.cast : ℤ → ℚ)
theorem solveWitness_det_ne_zero (h : solveWitness? A b fuel = some w) :
    Matrix.det (e A) ≠ 0
theorem solve_isSome_of_det_ne_zero (hA : Matrix.det (e A) ≠ 0)
    (hsupply : ∀ q ∈ ZMod64.primesBelow (2 ^ 31 - 1) (solveFuel A), 2 ^ 30 < q.m) :
    (solve? A b (solveFuel A)).isSome

theorem kernel_independent (h : kernel? A fuel = some K) :
    LinearIndependent ℚ (fun j : Fin (m - K.cert.rank) => v j)
theorem kernel_span (h : kernel? A fuel = some K) :
    Submodule.span ℚ (Set.range (fun j : Fin (m - K.cert.rank) => v j)) =
      LinearMap.ker (Matrix.mulVecLin M)
```

`det_eq` is the only one that needs the instance, and it is the total
theorem the Mathlib-free layer cannot state (see "The reconstruction").
The instance casts `A` to `Matrix (Fin n) (Fin n) ℝ`, applies
`norm_det_le_prod_norm_column` to `A` and to its transpose, bounds each
column's or row's real norm by `ceilSqrt` of the integer sum of squares,
and identifies the executable `det` with Mathlib's through
hex-determinant-mathlib's `det_eq` in
`HexDeterminantMathlib/CoreTransport.lean` (with `Int.cast` commuting
with `Matrix.det`). `det_eq` is then two cases: the `modular` route is
`detModular?_eq` under the instance plus that `det_eq`, and the
`bareiss` route is `HexMatrixMathlib.bareiss_eq_det` from
hex-bareiss-mathlib. `detWith_eq`, over every route including `divisor`,
is proved the same way once milestone 4 lands.

`rank_eq` is exactly `HexRankMathlib.checkRank_sound` at `R = Int`,
with no new proof of either rank bound. Applying it to `rankCert?_check h`
identifies a successful producer's result with the integer `Matrix.rank`.
`HexRankMathlib.rank_map_eq` at `IsFractionRing ℤ ℚ` identifies this with
the rank of `M` over `ℚ` (`algebraMap ℤ ℚ = Int.castRingHom ℚ`). It
says nothing about equality with rank over `ZMod p`. The fallback branch of `rankModular` uses hex-rank-mathlib's
`rank_eq` for `Hex.Matrix.rank`; together these give
`rankModular A = (e A).rank`.

`kernel_span` follows the statement and two-inclusion proof shape of
`HexRowReduceMathlib.nullspace_span_eq_ker` in
`HexRowReduceMathlib/RankSpanNullspace.lean`. That theorem takes an
`IsRowReduced` witness, which a `RankCert` is not, so it is a proof model,
not a theorem applied to the wrong certificate. Cast annihilation to
obtain membership of each `v j` in the kernel. The free coordinates are
`v j (F[k]) = -δ(k,j)`, proving `kernel_independent` by reading a zero
linear combination at each `F[k]`.

For the reverse inclusion, let `x ∈ ker M` and set
`y := ∑ j, (-x (F[j])) • v j`. Then `y ∈ ker M` and `x - y` has zero
free coordinates, so it is supported on `J`. Its selected-row equation
is `B * (x - y)[J] = 0` over `ℚ`. The checked certificate makes `B`
nonsingular, hence those remaining coordinates vanish and `x = y`.
This proves spanning without requiring the stored `adj` to be the
canonical adjugate. It also covers the empty basis at full column rank.

The solve theorems are transport and nothing more. `solve_eq` is
`solve?_spec` cast into `ℚ` and divided by `d`, which `0 < d` allows.
`solve_eq_inv` adds Mathlib's `Matrix.det ≠ 0`: `solveWitness_det_ne_zero`
is `solveWitness?_det_ne_zero` through hex-determinant-mathlib's
agreement between the executable `Matrix.det` and Mathlib's, and with
the determinant nonzero the cast matrix is a unit, so `solve_eq` rewrites
to the inverse form. That is the companion's statement of
`solve?_unique`, and it is stronger than the Mathlib-free one only in
naming the solution. `solve_isSome_of_det_ne_zero` is `decomp?_isSome`
and `solveWith_isSome` composed, with the `LawfulDetBound` hypothesis
discharged by the instance. `solveMat_eq` is `solveMatWith_spec`
transported the same way, and the rank section's `rank_eq` consumes it
through hex-rank's checker rather than directly. `solve_isSome_of_det_ne_zero`
inherits `decomp?_isSome`'s hypothesis that the primes tried exceed
`2^30`, stated as a hypothesis here too; the companion does not remove
the finite-supply obstruction, it only discharges the bound.

The determinant decidability instance follows, in the style of
hex-berlekamp-mathlib's `Decidable (Irreducible f)`:

```lean
instance (A : Matrix (Fin n) (Fin n) ℤ) : Decidable (A.det = 0)
```

The determinant instance uses its executable computation and correspondence.
`Decidable (A.rank = r)` for `A : Matrix (Fin n) (Fin m) ℤ` is already
supplied by hex-rank-mathlib: import and reuse that instance, without
declaring an overlapping instance here. A modular decision procedure can branch on `rankCert?`, use `checkRank_sound` for a successful
certificate, and on `none` use the total
`rankCertWith HexArith.Int.exactDiv` certificate with its correctness
theorem. Equality of the certified natural rank with `r` then decides
`A.rank = r`; an unchecked modular image never decides the proposition.

Following the project split, no theorem about `Crt` or `RankCert` belongs
in the companion beyond these and one correspondence lemma per public
operation.

## Milestones

1. **One image.** `Matrix.mapEntries` (in hex-matrix) with
   `det_mapEntries` (in hex-determinant), `ZMod64.inv?` (in
   hex-mod-arith), `detMod?`, `detMod?_eq`, and `detMod?_reduce`.
   Nothing multi-modular yet, and everything that follows depends on it.

2. **The determinant.** The two CRT lemmas (in hex-modular),
   `rowNormBound` with `natAbs_det_le_rowNormBound`, `hadamardBound`,
   `LawfulDetBound`, `detBounded?`, `detModular?`, `detBounded?_eq`,
   `detModular?_eq`, and the `Hex.ModularMatrix` wrappers `detWith` and
   `det` with their route equations. At the end of this milestone the
   modular route is proved correct, unconditionally at the row-norm
   bound and under `[LawfulDetBound]` at the Hadamard one, and there is
   no performance claim.

3. **The Dixon solve.** `Decomp`, `decompAt?`, `decomp?`, `Decomp.lift`,
   `solveWith`, `solve?`, `solveWitness?`, then `solveMatWith` and
   `solveMat?`: the exact division step, `numeratorBound` and the digit
   count, the normalisation, and the check. `solve?_spec` and
   `solve?_reduced` need no hypothesis, `solve?_unique` needs only
   nonsingularity, and `decomp?_isSome` and `solveWith_isSome` carry
   `[LawfulDetBound]` (the second through hex-modular's
   `ratReconVec?_complete`). The rank milestone's `r` solves and
   the next milestone's single solve both go through `Decomp`.

4. **The determinant divisor.** `dvd_det_of_mulVec`,
   `detViaDivisorWith` and `detViaDivisorWith_eq`, wired into
   `detWith`'s `divisor` route, with the random right-hand side drawn
   from `Hex.Rand`. This is the milestone that produces the
   benchmark numbers, and the route-level test for the reduction step is
   written before the code.

5. **Rank.** Import `Hex.Matrix.RankCert Int` and `Hex.Matrix.checkRank`;
   add `rankModP`, `rankCert?`, `rankCert?_check`, and `rankModular` using
   the reusable decomposition. Add `Kernel`, `kernel?`, annihilation and
   free-block facts; the companion reuses `checkRank_sound` and proves
   `kernel_independent` and `kernel_span`. This milestone requires the
   hex-rank certificate/profile producer and companion, and milestone 3's
   decomposition and repeated-solve design from #10178 to be specified
   and implemented first.

6. **The companion.** Begins as soon as milestone 2 is done, in parallel
   with 3 through 5. The `LawfulDetBound` instance and the total `det_eq`
   are its first two theorems.

## File organisation

```
HexModularMatrix/
  Image.lean        -- detMod?, detMod?_eq, detMod?_reduce
  Bound.lean        -- rowNormBound and its proof, hadamardBound, LawfulDetBound
  Det.lean          -- detBounded?, detModular?, their theorems, and the Hex.ModularMatrix wrappers
  Dixon.lean        -- Decomp, decompAt?, decomp?, numeratorBound, solveFuel,
                    --   Decomp.lift, solveWith, solveMatWith, solve?,
                    --   solveMat?, solveWitness?
  Divisor.lean      -- dvd_det_of_mulVec, detViaDivisorWith, detViaDivisorWith_eq
  Rank.lean         -- rankModP, rankCert?, rankCert?_check, rankModular (imports HexRank)
  Kernel.lean       -- Kernel, kernel?, annihilation and free-block facts
HexModularMatrix.lean
HexModularMatrixMathlib/
  Bound.lean        -- the LawfulDetBound instance
  Det.lean          -- det_eq and detWith_eq (total, via bareiss_eq_det), Decidable (A.det = 0)
  Rank.lean         -- rank_eq via HexRankMathlib, rankModular_eq, kernel_independent, kernel_span
  Solve.lean        -- solve_eq, solve_eq_inv, solveMat_eq,
                    --   solveWitness_det_ne_zero, solve_isSome_of_det_ne_zero
HexModularMatrixMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexModularMatrix:
    deps: [HexModular, HexMatrix, HexRowReduce, HexRank, HexDeterminant, HexBareiss, HexModArith, HexArith, HexBasic]
    mathlib: false
    done_through: 0
    status: planned
    phase4:
      comparators:
        - tool: FLINT fmpz_mat_det via python-flint
          class: gating
          goal: detViaDivisor faster than Hex.Matrix.bareiss by at least 4x at n = 512 on the shared tridiagonal fixture in the same run (2.2x FLINT on the current report), with the FLINT ratio recorded and the 5x target at every eligible rung reviewed after the first measurement
        - tool: FLINT fmpz_mat_rank via python-flint
          class: informational
          rationale: no shared fixture history and a different crossover policy
        - tool: FLINT fmpq_mat_solve via python-flint
          class: informational
          rationale: FLINT dispatches between fraction-free, multi-modular and Dixon solvers with tuned crossovers, and its solve does not expose a reusable decomposition, so the repeated-solve family has no FLINT counterpart
      input_families:
        - name: structured-determinant
          description: the deterministic tridiagonal fixture shared with HexBareiss.Bench
        - name: dense-random-determinant
          description: dense random matrices at 8, 64, and 1024 bit entries
        - name: unimodular-determinant
          description: matrices of determinant plus or minus one, the worst case for the divisor
        - name: rank
          description: square and rectangular matrices at several ranks, measuring rankCert? and rankModular
        - name: rank-bad-primes
          description: large-coefficient rank-deficient s L R matrices, with s the product of initial producer primes, requiring skips and a successful certificate
        - name: solve
          description: single right-hand sides with integral and with large-denominator solutions, at n = 32 to 256, measuring decomp? and solveWith separately
        - name: repeated-solve
          description: r right-hand sides against one matrix through one decomposition, at r = 1, 8, n, against r independent solve? calls, measuring what the decomposition saves
  HexModularMatrixMathlib:
    deps: [HexModularMatrix, HexRankMathlib, HexMatrixMathlib, HexDeterminantMathlib, HexBareissMathlib, HexRowReduceMathlib, HexModularMathlib, HexPolyZMathlib]
    mathlib: true
    done_through: 0
    status: planned
```

`HexDeterminant` supplies the reference `det`, the row-operation lemmas,
and the Laplace expansion behind `rowNormBound`. Nothing here evaluates
the Leibniz sum at runtime. `HexBareiss` supplies the total determinant
fallback, and `HexBareissMathlib` is where its determinant equation
lives. `HexPolyZMathlib` is where the Hadamard proof lives until it
moves. `HexBasic` is for `Hex.Rand`, the generator the determinant divisor
draws its right-hand side from.

## Open questions

- **Whether `detMod?` should use Barrett or Montgomery reduction.**
  The inner loop is a multiply-subtract modulo a 31-bit modulus, `n³`
  times per image, and hex-arith has both reductions. Which one wins
  depends on whether the modulus is fixed across the whole image (it is)
  and on how many products can be accumulated before a reduction, which
  the `ZMod64` bound was chosen to allow. This is a measurement, and it
  is the single largest constant factor in the library.
- **Whether the images should be computed in blocks.** Reducing the
  matrix modulo several moduli at once and eliminating them together
  shares the memory traffic, and hex-matrix's `Strassen` and `Winograd`
  suggest the blocking machinery is available. Worth measuring after
  milestone 4, not before.
- **The determinant does not also produce a rank witness.** Its scalar
  result does not supply the selected minor and adjugate required by
  `Hex.Matrix.RankCert Int`; callers needing rank evidence use `rankCert?`
  (or hex-rank's total producer) separately.
- **The crossover with Bareiss.** The benchmark will show a size below
  which the fraction-free path is faster, and the dispatch should use it.
  This SPEC does not guess the number.
