# hex-modular-matrix (multi-modular determinant, certified rank, Dixon lifting)

Exact linear algebra over `ℤ` and `ℚ` computed through modular images:
the determinant of an integer matrix from its residues modulo many
moduli, the rank with a two-sided certificate, and the solution of
`A x = b` over `ℚ` by `p`-adic lifting. Mathlib-free. The companion
`hex-modular-matrix-mathlib` discharges the determinant bound the
Mathlib-free layer carries as a hypothesis, and identifies the executable
results with `Matrix.det`, `Matrix.rank`, and `Matrix.mulVec`.

This SPEC expands three of the five bullets in the "Modular techniques"
entry of [future-work](../future-work.md), and depends on the
reconstruction operations specified in [hex-modular](hex-modular.md). The
fourth bullet, the modular gcd for `ℤ[x]`, is
[hex-poly-z-gcd](hex-poly-z-gcd.md); the fifth, rational reconstruction
itself, is in [hex-modular](hex-modular.md).

## Why this library exists

**The gap is measured, and it is a factor of twenty.**
[reports/hex-bareiss-performance.md](../../reports/hex-bareiss-performance.md)
records `Hex.Matrix.bareiss` against FLINT's `fmpz_mat.det` on the same
deterministic tridiagonal fixture. The raw ratio crosses unity at
`n = 128` and reaches `0.062x` at `n = 512`; on the rungs where the
harness startup cost is small enough for the comparison to be eligible
(`n = 320, 384, 512`) the adjusted ratio sits at `0.049x` to `0.057x`.
FLINT spends about five percent of Hex's wall time on the same
determinant, and the gap widens with `n`.

hex-bareiss's SPEC classifies that comparator as `informational` for a
stated reason: FLINT uses multi-modular reduction with Chinese
remaindering, and Bareiss is fraction-free elimination over `Int`, so the
two have different asymptotic and constant-factor profiles. The report's
own recommendation is to add "a multimodular CRT path layered over the
existing Bareiss kernel". This library is that path, and implementing it
is what turns the comparison into a like-for-like one, which is exactly
what [future-work](../future-work.md) says.

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
kernel bases in [hex-hermite](hex-hermite.md), and the certified rank
below all want an exact solve that does not pay that growth. Dixon
lifting is the standard answer and its output is checkable by one
matrix-vector product.

**hex-hermite needs a determinant.** The Domich-Kannan-Trotter modular
Hermite algorithm reduces entries modulo a determinant of a square
nonsingular submatrix, and [hex-hermite](hex-hermite.md) names
hex-bareiss as the supplier. The determinant here is the faster supplier
for exactly the sizes where the modular Hermite path is worth taking.

## What has a checker and what does not

[future-work](../future-work.md) opens with a warning that a positive
certificate establishes only what it carries a witness for. Applied to
this library, the three operations come out differently, and the
difference drives the whole design.

**The linear solve has a one-line checker.** A claimed solution `y/d`
is accepted by testing `A y = d b` over `ℤ`, which is one matrix-vector
product. Everything that produced it (the prime, the inverse modulo `p`,
the lifting, the reconstruction) runs untrusted.

**The rank has a two-sided certificate.** A lower bound is a square
submatrix whose determinant is nonzero modulo one modulus, which is
cheap and conclusive because a nonzero residue of an integer proves the
integer nonzero. An upper bound is a rational expression of every other
column in terms of the chosen ones, which is a matrix product to check.
Neither half alone settles the rank, and together they settle it exactly.

**The determinant has no cheap checker.** Verifying `det A = d` is, as
far as anyone knows, no easier than computing it: the natural witnesses
(the adjugate, a triangular factorisation) are the size of the answer
times `n`, and checking them costs another `n³` big-integer
multiplications. So the multi-modular determinant is a *proved algorithm*
rather than a checked candidate, and it carries the only analytic
hypothesis in this library. Everything downstream of that difference,
including which reconstruction rule may be used and which may not, is
recorded below where it applies.

That asymmetry has one further consequence worth stating in advance.
Certified dispatch to an untrusted external implementation, in the shape
`hex-lll`'s `certCheck` uses for fpLLL and [hex-hermite](hex-hermite.md)
specifies for Hermite forms, is available for the solve and for the rank
and is **not** available for the determinant. An external determinant
would have to be trusted, and design principle 4 forbids that.

## Two corrections to the future-work entry

**Primality is not among the checker's obligations.** That entry says
they are "primality and distinctness of the moduli, the CRT congruences,
and a reconstruction bound large enough to determine the answer". The
determinant argument never uses primality: reduction modulo any `m` is a
ring homomorphism, so `det (A mod m) = (det A) mod m` regardless, and
what the *elimination* needs is that the pivots it inverts are units,
which the arithmetic discovers rather than assumes. Distinctness is not
the right property either, since distinct moduli need not be coprime;
coprimality is what the reconstruction needs and `Crt.push` checks it.
[hex-modular](hex-modular.md) sets this out in full under "Primality is
not what the checkers need". Primality does appear here, once: the rank
of an image modulo `p` is a rank only when `F_p` is a field, and the
statement of `rankModP` says so.

**Reduction mod `p` dropping the rank is not by itself the lower
bound.** The entry says "Reduction mod `p` can only drop rank, so the
modular computation supplies a lower bound on the rational rank." The
conclusion is right and the reason as stated is circular: the modular
rank is a lower bound because a nonvanishing `r × r` minor modulo `p` is
a nonvanishing integer minor, and that argument produces the *witness*
the certificate carries. Phrasing it as "reduction can only drop rank"
suggests the modular computation is the evidence, when in fact the
submatrix is.

## Scope

In scope: the determinant of a square integer matrix; the rank of a
rectangular integer matrix with a certificate; the solution of a square
nonsingular integer system over `ℚ`; a rational kernel basis; and the
determinant divisor optimisation that links the first to the third.

Not in scope for the first version: rectangular and inconsistent systems
(the certificate shape differs and the consistency question is a rank
question); matrix inversion as a returned object, since every consumer
here wants a solve rather than an inverse; the Smith and Hermite normal
forms, which are [hex-smith](hex-smith.md) and
[hex-hermite](hex-hermite.md) and want this library rather than replace
it; and the characteristic polynomial, whose multi-modular form is a
separate entry in [future-work](../future-work.md) and is a consumer of
this one.

Coefficients are `Int` throughout. A rational input is cleared to an
integer matrix and a scalar denominator by the caller, and the API says
so rather than accepting `Rat` matrices and doing it silently.

## The determinant

### One image

```lean
namespace Hex.Matrix

/-- The determinant of `A` reduced modulo `m`, computed by elimination.
Returns `none` when a pivot candidate is not invertible modulo `m`, which
for composite `m` can happen without the matrix being singular. -/
def detMod? (A : Matrix (ZMod64 m) n n) : Option (ZMod64 m)
```

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
  be prime. `detMod?` is written against the `Option`-returning inverse
  and works at any modulus, which is what lets the reconstruction argument
  drop primality.

Correctness comes from the row-operation determinant lemmas that
hex-determinant already proves: `det_rowSwap`, `det_rowScale`, and
`det_rowAdd` in `HexDeterminant/RowOps.lean`. The loop invariant is that
the product of the pivots so far, times the sign of the accumulated
permutation, times the determinant of the untouched trailing submatrix,
equals `det A`.

```lean
theorem detMod?_eq (h : detMod? A = some d) : Matrix.det A = d
theorem detMod?_reduce (A : Matrix Int n n) :
    detMod? (A.mapEntries (ZMod64.intCast m)) = some d →
      (Matrix.det A) % (m : Int) = d.toInt % (m : Int)
```

The second is the reduction homomorphism, and it holds for every modulus.

### The bound

```lean
/-- The Hadamard bound: the product over columns of the ceiling of the
Euclidean norm. An upper bound for `|det A|`. -/
def hadamardBound (A : Matrix Int n n) : Nat

/-- The one analytic fact the multi-modular determinant rests on.
Discharged in `hex-modular-matrix-mathlib`. -/
class LawfulDetBound : Prop where
  abs_det_le : ∀ {n} (A : Matrix Int n n), (Matrix.det A).natAbs ≤ hadamardBound A
```

Hadamard's inequality is an analytic statement (it is a Gram-matrix
inequality, and the sharp form goes through Gram-Schmidt), so under
design principle 2 the Mathlib-free layer states it and the companion
proves it. The companion has almost nothing to do, because the proof
already exists: `Matrix.norm_det_le_prod_norm_column` in
`HexPolyZMathlib/Hadamard.lean` is the sharp column form over an
`RCLike` field, written for the Mahler separation bound. That it lives in
a polynomial library is a placement error, and moving it is one of the
relocations below.

**The alternative that avoids the hypothesis, and what it costs.**
The Leibniz expansion gives `|det A| ≤ n! · B^n` for `B` the largest
entry, and that is an elementary bound with a Mathlib-free proof. It is
not adopted, for two reasons. It needs
`(permutationVectors n).length = n !`, which hex-determinant does not
prove today (the enumeration is in `HexDeterminant/Enumeration.lean` and
carries inversion-count and nodup lemmas, not a length). And it is worse
by `n log₂ n / 2 - 1.44 n` bits, which at small entries is close to a
factor of two in the number of moduli and at large entries is
negligible beside the `n log₂ B` term. The right resolution is to state
the good bound as a hypothesis and discharge it, and to record the crude
bound here as the fallback if a Mathlib-free consumer ever appears.

### The reconstruction

```lean
/-- The determinant of an integer matrix, by Chinese remaindering over
enough moduli to determine it. -/
def det (A : Matrix Int n n) : Int

theorem det_eq [LawfulDetBound] (A : Matrix Int n n) :
    det A = Matrix.det A
```

The loop folds one image per modulus into a `Crt` and stops when the
accumulated modulus exceeds `2 · hadamardBound A`, at which point
`crt_unique` identifies the symmetric representative with the answer.
Moduli at which `detMod?` returns `none` are skipped.

**Early termination is not available here, and this is the one place in
the tree where that has to be said out loud.** Stopping when the
reconstructed value stops changing across two further moduli is what a
consumer with a check may do, and this operation has no check. A
determinant produced by a stabilisation rule is a guess. The bound is
therefore not an optimisation to be tuned away; it is the correctness
argument. The next subsection is how to make the bound small rather than
how to avoid it.

### The determinant divisor

The Hadamard bound is pessimistic by a wide margin on almost every input,
and the standard remedy, due to Abbott, Bronstein, and Mulders ("Fast
deterministic computation of determinants of dense matrices", ISSAC
1999), removes the pessimism without weakening the argument.

Solve `A x = b` for a random `b` by the Dixon solve below, obtaining `y`
and `d > 0` with `A y = d b` and the pair reduced. The random vector is
drawn from a seedable generator under the discipline the equal-degree
splitting item in [future-work](../future-work.md) sets: the generator
state is an explicit argument rather than a monad, the seed is a
parameter of the public entry point so a run is reproducible, and the
draw affects how many moduli the run needs and never what it returns.
The tree has no such generator today, so the first consumer to land
writes it, and it belongs in hex-basic rather than here. Then `d` divides
`det A`, so the remaining factor `det A / d` is bounded by
`hadamardBound A / d`, and Chinese remaindering only has to determine
that much smaller number.

```lean
/-- The determinant, computed as a divisor found by lifting times a
cofactor found by Chinese remaindering. -/
def detViaDivisor (A : Matrix Int n n) : Int
```

Three things make this rigorous rather than heuristic, and the middle one
is easy to get wrong:

- `d ∣ det A` needs Cramer's rule. From `A y = d b` with `A` nonsingular,
  `y_i / d = det(A_i) / det(A)`, so `det(A) · y_i = d · det(A_i)` for
  every `i`, so `d` divides `det(A) · gcd_i(y_i)`.
- **The pair must be reduced first.** The divisibility conclusion needs
  `gcd(gcd_i y_i, d) = 1`. Dixon's reconstruction returns a common
  denominator that need not be the least one
  ([hex-modular](hex-modular.md) says so explicitly under "Vectors with a
  common denominator"), so `detViaDivisor` divides `y` and `d` through by
  their common gcd before using `d`. Omitting that step gives a `d` that
  does not divide the determinant and a wrong answer with no symptom.
- The cofactor still needs a bound, and it has one: `|det A / d| ≤
  hadamardBound A / d`, from the same hypothesis as before. Nothing is
  assumed about how large `d` is. A small `d` costs moduli, never
  correctness.

Nonsingularity is not an extra assumption. The Dixon solve inverts `A`
modulo a prime, and a matrix invertible modulo `p` has a determinant that
is nonzero modulo `p`, hence nonzero. When the solve fails to find such a
prime after its budget, `detViaDivisor` falls back to `det` above.

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

/-- A certificate for the rank of an integer matrix. -/
structure RankCert (n m : Nat) where
  /-- The claimed rank. -/
  r : Nat
  /-- Row and column indices of a nonsingular `r × r` submatrix. -/
  rows : Vector (Fin n) r
  cols : Vector (Fin m) r
  /-- A modulus at which that submatrix has nonzero determinant. -/
  modulus : Modulus
  /-- Coefficients expressing the remaining columns over the chosen ones,
  with a common denominator. -/
  coeffs : Matrix Int r (m - r)
  denom : Int

def checkRank (A : Matrix Int n m) (c : RankCert n m) : Bool

theorem checkRank_sound (h : checkRank A c = true) : rank A = c.r
```

`checkRank` verifies, cheapest first: that `rows` and `cols` are strictly
increasing (so the submatrix is well formed and the complement of `cols`
is determined); that `detMod?` of the selected `r × r` submatrix is
`some` and nonzero; that `denom ≠ 0`; and that
`A[·, cols] * coeffs = denom · A[·, colsᶜ]` as an integer matrix
identity.

The two halves of the argument:

- The nonzero residue proves the `r × r` minor is a nonzero integer, so
  those `r` columns are linearly independent over `ℚ` and `rank A ≥ r`.
  This needs no primality, and it is why `modulus` is a `Modulus` rather
  than a `PrimeModulus`.
- The matrix identity places every remaining column in the rational span
  of the chosen `r`, so the column space has dimension at most `r` and
  `rank A ≤ r`.

**Producing a certificate.** Reduce modulo a prime, read the pivot rows
and columns off `rowReduce`, and Dixon-solve `A[·, cols] X = A[·, colsᶜ]`
for the coefficients. A bad prime makes `rankModP` too small, the chosen
column set too small, and the span check fail on some column; the
response is another prime. The modular rank is never too large, by the
minor argument above, so a failure always means "try again" and never
means "the answer is wrong".

```lean
def rankCert? (A : Matrix Int n m) (fuel : Nat) : Option (RankCert n m)
def rank (A : Matrix Int n m) : Nat
```

`rank` is `rankCert?` with a default budget, falling back to row
reduction over `Rat` when the budget runs out. Under design principle 8
that fallback is an `audited-emergency-value` in neither sense: it is a
second complete algorithm, not a default, and its result is correct on
its own terms. The API exposes `rankCert?` so that a caller who wants the
witness can have it.

## The Dixon solve

```lean
/-- Solve `A x = b` over `ℚ` by `p`-adic lifting. Returns the numerator
vector and the common denominator of `x`, reduced. -/
def solve? (A : Matrix Int n n) (b : Vector Int n) (fuel : Nat) :
    Option (Vector Int n × Int)

theorem solve?_spec (h : solve? A b fuel = some (y, d)) :
    A.mulVec y = d • b ∧ 0 < d

theorem solve?_unique (h : solve? A b fuel = some (y, d))
    (hA : Matrix.det A ≠ 0) (hz : A.mulVec z = e • b) (he : 0 < e) :
    e • y = d • z
```

The algorithm, with the two steps that are easy to state wrongly marked:

1. Find a prime `p` at which `A` is invertible, and compute `B` with
   `B A ≡ I (mod p)`. This is the only `O(n³)` step, and it is done once.
2. Set `r₀ = b`. Repeat: `xᵢ = B rᵢ mod p`, then
   `rᵢ₊₁ = (rᵢ - A xᵢ) / p`. **The division is exact**, because
   `A xᵢ ≡ A B rᵢ ≡ rᵢ (mod p)`, and it is a division rather than a
   shift because `p` is not a power of two. This is where hex-arith's
   `exactDiv` belongs.
3. After `k` steps, `x ≡ Σ xᵢ pⁱ (mod p^k)`, so the solution is known
   modulo `p^k`.
4. Reconstruct with `ratReconVec?` at bounds `P = hadamardBound Ab` and
   `Q = hadamardBound A`, where `Ab` is `A` with one column replaced by
   `b`. **The number of steps is set by `p^k > 2 P Q`**, from Cramer's
   rule: the numerators are minors of `Ab` and the denominator divides
   `det A`.
5. Check `A y = d b` over `ℤ` and return `none` if it fails.

Because of step 5 the whole thing is a checked candidate. `solve?_spec`
follows from the check alone and needs no hypothesis, not even
`LawfulDetBound`: the bound governs how many lifting steps are enough,
which is a question about whether the check will pass rather than about
what it means when it does.

`solve?_unique` is the other half, and the hypothesis it needs is
nonsingularity, which the caller gets for free from step 1: a matrix
invertible modulo `p` has nonzero determinant. The API therefore also
offers

```lean
/-- The prime at which `A` was inverted, which witnesses `det A ≠ 0`. -/
def solveWitness? (A : Matrix Int n n) (b : Vector Int n) (fuel : Nat) :
    Option (Vector Int n × Int × Modulus)
```

so a consumer can carry the nonsingularity evidence rather than
recompute it.

**Rational input, rational right-hand side.** A caller with `Rat` data
clears denominators. `solve?` does not accept `Rat`, because the
clearing is a scalar multiplication the caller can do exactly once, and
accepting `Rat` would invite it to be done per call.

## Rational kernel basis

```lean
/-- A basis of the rational kernel, as integer columns with a common
denominator, in reduced column echelon shape against the free columns. -/
def kernel? (A : Matrix Int n m) (fuel : Nat) : Option (Matrix Int m (m - r))
```

This is the rank certificate's coefficient matrix rearranged: with pivot
columns `J` and coefficients `C` satisfying `A_J C = d A_{Jᶜ}`, the
columns `(C, -d I)` reindexed span the kernel. Because the free block is
`-d I`, the returned matrix has full column rank by inspection, which is
what makes the dimension count part of the certificate rather than a
further obligation.

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
| `detViaDivisor` | one solve plus `⌈log₂(H/d)/w⌉` images | `O(n³ + n² h)` typical | small |
| `solve?` | one inverse plus `k = O(h/w)` steps | `O(n³ + n² h / w)` | `O(n·h)` in the reconstruction |
| `rankCert?` | one modular reduction plus `m - r` solves | `O(n m r + (m-r) · n²h/w)` | check is `O(n r (m-r))` at size `h` |
| `checkRank` | one integer matrix product | none | `O(n r (m-r))` at size `h` |
| `Hex.Matrix.bareiss` | fraction-free elimination | none | `O(n³)` at size up to `h` |

The last two rows are the comparison. Bareiss performs `n³`
multiplications on integers that grow to the size of the answer, so its
bit cost carries a factor of `h` (and, with schoolbook multiplication, of
`h²`). The multi-modular determinant performs `n³ h / w` multiplications
on machine words. Dixon replaces the `h` in the first factor by a single
`O(n³)` inverse plus `O(n²)` per digit, which is where its advantage over
both comes from.

## Prerequisite changes in other libraries

Five, of which three are shared with other planned libraries and are
listed here because this library is a second consumer.

**`zmod64FieldOfPrime` should move to hex-mod-arith.** Set out in
[hex-modular](hex-modular.md). Without it, `rankModP` forces a dependency
on hex-poly-fp for one instance about a `ZMod64` type.

**An entrywise `Matrix.mapEntries` is missing.** hex-matrix has
`mapRows`, `mapRowsIdx`, and `modifyEntries`, and no entrywise map. Reducing an
integer matrix modulo `m` and lifting a residue matrix back are the two
most-executed operations in this library, and both are entrywise maps.
The function belongs in hex-matrix next to `mapRows`, with the linear
buffer discipline design principle 3 requires, and with the `getElem`
characterisation lemma.

**`floorSqrt` and `ceilSqrt` should move to hex-arith**, from
`HexPolyZ/Mignotte.lean` where they sit under the `Hex.ZPoly` namespace.
`hadamardBound` computes one integer square root per column.

**`exactDiv` should move to hex-arith**, from `HexBareiss/Bareiss.lean`.
[hex-hermite](hex-hermite.md) already asks for this. Dixon's lifting step
divides an exactly-divisible vector by `p` once per digit, which is the
hottest exact division in the tree.

**Hadamard's inequality should move to hex-matrix-mathlib.**
`HexPolyZMathlib/Hadamard.lean` proves
`Matrix.norm_det_le_prod_norm_column` for Mathlib matrices over an
`RCLike` field. It is a determinant inequality with no polynomial content,
`HexRealRootsMathlib/Hadamard.lean` already exists solely as a
compatibility import of it across libraries, and this library's companion
would be a third cross-library consumer. Move the file to
hex-matrix-mathlib and leave compatibility imports in both current
places.

None of the five blocks starting work here.

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
have.** `det` and `detViaDivisor` return the same value, and `rank`
falls back to row reduction over `Rat`, so an end-to-end fixture passes
even if the determinant divisor is never used, the unlucky-prime path
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
  one enormously below it (a triangular matrix with unit diagonal), which
  are the two ends the determinant divisor is designed to separate.
- A determinant of `±1`, where the divisor is `1` and no shortcut helps.
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
  `HexBareiss.Bench` uses, at the same rungs `n = 16 … 512`. Using the
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
  nearly full.
- **Solve**, with integral solutions and with large-denominator
  solutions.

**Comparators.** FLINT's `fmpz_mat_det` becomes `gating` here, and this
is the one classification change this SPEC makes to an existing
comparator relationship. hex-bareiss classifies it `informational`
because the algorithms differ; once this library implements the same
algorithm the comparison is like-for-like and the reason for the
exemption is gone. Two thresholds, written down in advance:

- **Against `Hex.Matrix.bareiss`**, on the shared tridiagonal fixture,
  `detViaDivisor` must be faster at every rung `n ≥ 64`, and faster by at
  least `4x` at `n = 512`. This is a required check, and failing it means
  the library has not earned its place.
- **Against FLINT `fmpz_mat.det`**, on the same fixture and using the
  same startup-adjusted ratio the existing report defines,
  `detViaDivisor` must be within `5x` at every eligible rung. `5x` is
  chosen as a plausible constant factor between Lean and tuned C over
  GMP, given that the algorithms then agree; it is a written-down
  threshold, to be revised only with measurements and a stated reason.

FLINT's `fmpz_mat.rank` and `fmpq_mat.solve` are `informational`: FLINT's
solve uses a tuned multi-modular and Dixon hybrid with a different
crossover policy, and there is no shared fixture history to anchor a
required ratio.

## The Mathlib layer

`hex-modular-matrix-mathlib` discharges the hypothesis and transports the
results. Writing `e` for hex-matrix-mathlib's `matrixEquiv`:

```lean
instance : LawfulDetBound        -- from Matrix.norm_det_le_prod_norm_column

theorem det_eq (A : Matrix Int n n) : det A = Matrix.det (e A)
theorem rank_eq (A : Matrix Int n m) : rank A = Matrix.rank (e A)

theorem solve_eq (h : solve? A b fuel = some (y, d)) :
    Matrix.mulVec (e A) (fun i => (y[i] : ℚ) / d) = fun i => (b[i] : ℚ)

theorem kernel_span (h : kernel? A fuel = some K) :
    Submodule.span ℚ (Set.range (e K).col) = LinearMap.ker (Matrix.mulVecLin (e A))
```

`det_eq` is the only one that needs the instance. Getting from the
Mathlib-free `det_eq [LawfulDetBound]` to this unconditional statement is
the discharge plus hex-determinant-mathlib's existing agreement between
the executable `Matrix.det` and Mathlib's.

`rank_eq` needs `Matrix.rank` over `ℚ` of the integer matrix cast into
`ℚ`, which is the standard meaning of the rank of an integer matrix and
is what the certificate establishes. The statement over `ZMod p` is
different and is not claimed.

Two decidability instances follow, in the style of
hex-berlekamp-mathlib's `Decidable (Irreducible f)`:

```lean
instance (A : Matrix (Fin n) (Fin n) ℤ) : Decidable (A.det = 0)
instance (A : Matrix (Fin n) (Fin m) ℤ) (r : Nat) : Decidable (A.rank = r)
```

Both are the executable computation plus the correspondence, and both are
worth having because Mathlib's own definitions are noncomputable.

Following the project split, no theorem about `Crt` or `RankCert` belongs
in the companion beyond these and one correspondence lemma per public
operation.

## Milestones

1. **One image.** `Matrix.mapEntries` (in hex-matrix), the
   `Option`-returning modular inverse, `detMod?`, and its two theorems.
   Nothing multi-modular yet, and everything that follows depends on it.

2. **The determinant.** `hadamardBound`, `LawfulDetBound`, the moduli
   loop, `det`, and `det_eq`. At the end of this milestone the library
   has a correct determinant and no performance claim.

3. **The Dixon solve.** `solve?`, `solveWitness?`, the exact division
   step, the digit count, and the check. `solve?_spec` needs no
   hypothesis, and `solve?_unique` needs only nonsingularity.

4. **The determinant divisor.** `detViaDivisor`, with the reduction step
   and its divisibility lemma. This is the milestone that produces the
   benchmark numbers, and the route-level test for the reduction step is
   written before the code.

5. **Rank.** `rankModP`, `RankCert`, `checkRank`, `checkRank_sound`,
   `rankCert?`, `rank`, and `kernel?`.

6. **The companion.** Begins as soon as milestone 2 is done, in parallel
   with 3 through 5.

## File organisation

```
HexModularMatrix/
  Image.lean        -- detMod?, the Option-returning inverse, reduction lemmas
  Bound.lean        -- hadamardBound, LawfulDetBound
  Det.lean          -- det, the moduli loop, det_eq
  Dixon.lean        -- solve?, solveWitness?, the lifting loop
  Divisor.lean      -- detViaDivisor and the divisibility argument
  Rank.lean         -- rankModP, RankCert, checkRank, rankCert?, rank, kernel?
HexModularMatrix.lean
HexModularMatrixMathlib/
  Bound.lean        -- the LawfulDetBound instance
  Det.lean          -- det_eq, Decidable (A.det = 0)
  Rank.lean         -- rank_eq, kernel_span, Decidable (A.rank = r)
  Solve.lean        -- solve_eq
HexModularMatrixMathlib.lean
```

`libraries.yml` gains:

```yaml
  HexModularMatrix:
    deps: [HexModular, HexMatrix, HexRowReduce, HexDeterminant, HexModArith, HexArith, HexBasic]
    mathlib: false
    done_through: 0
    status: planned
    phase4:
      comparators:
        - tool: FLINT fmpz_mat_det via python-flint
          class: gating
          goal: within 5x on the shared tridiagonal fixture at every eligible rung
        - tool: FLINT fmpz_mat_rank via python-flint
          class: informational
          rationale: no shared fixture history and a different crossover policy
        - tool: FLINT fmpq_mat_solve via python-flint
          class: informational
          rationale: FLINT dispatches between multi-modular and Dixon with tuned crossovers
      input_families:
        - name: structured-determinant
          description: the deterministic tridiagonal fixture shared with HexBareiss.Bench
        - name: dense-random-determinant
          description: dense random matrices at 8, 64, and 1024 bit entries
        - name: unimodular-determinant
          description: matrices of determinant plus or minus one, the worst case for the divisor
        - name: rank
          description: square and rectangular matrices at several ranks
        - name: solve
          description: systems with integral and with large-denominator solutions
  HexModularMatrixMathlib:
    deps: [HexModularMatrix, HexMatrixMathlib, HexDeterminantMathlib, HexRowReduceMathlib, HexModularMathlib]
    mathlib: true
    done_through: 0
    status: planned
```

`HexDeterminant` is a dependency for the row-operation determinant
lemmas, not for the Leibniz determinant, which nothing here calls.
`HexBasic` is for the random generator the determinant divisor draws
its right-hand side from.

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
- **Whether `solve?` should return the `p`-adic expansion.** A consumer
  that wants the solution modulo `p^k` rather than as a rational (a
  Hensel-style consumer, or [hex-hermite](hex-hermite.md)'s modular path)
  currently has to reconstruct and re-reduce. Exposing the expansion
  costs an API and would let the reconstruction be skipped entirely where
  the caller does not need it.
- **Whether the determinant should also produce a rank witness.** A
  singular matrix currently returns `0` with no evidence, and the caller
  who wants to know why runs `rankCert?` separately, repeating the
  elimination. Merging them is attractive and would complicate the
  determinant's loop, which is the hottest code here.
- **The crossover with Bareiss.** The benchmark will show a size below
  which the fraction-free path is faster, and the dispatch should use it.
  This SPEC does not guess the number.
