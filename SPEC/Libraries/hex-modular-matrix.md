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
reconstruction operations specified in [hex-modular](../../HexModular/SPEC/hex-modular.md). The
fourth bullet, the modular gcd for `ℤ[x]`, is
[hex-poly-z-gcd](../../HexPolyZGcd/SPEC/hex-poly-z-gcd.md); the fifth, rational reconstruction
itself, is in [hex-modular](../../HexModular/SPEC/hex-modular.md).

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
which the arithmetic discovers rather than assumes. `detMod?` returning
`some d` at a composite modulus is as good an image as any. Distinctness is not
the right property either, since distinct moduli need not be coprime;
coprimality is what the reconstruction needs and `Crt.push` checks it.
[hex-modular](../../HexModular/SPEC/hex-modular.md) sets this out in full under "Primality is
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

### Public names and dispatch integration

The executable wrappers `det` and `detViaDivisor` below belong in
`Hex.ModularMatrix`, not `Hex.Matrix`: `Hex.Matrix.det` already denotes the
Leibniz reference and cannot be redeclared. Their conditional correctness
lemmas use that wrapper namespace. Mathlib correspondence remains in the
companion namespace. Image, bound, and partial reconstruction operations
remain in `Hex.Matrix`. The shared dispatcher is `Hex.Det.det` in
[hex-det](hex-det.md), above this library.

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

The implementation owes `detWith_eq`, under
`[Hex.Matrix.LawfulDetBound]`, asserting that every returned value equals
`Hex.Matrix.det A`, and route equations for each success and failure branch.
These are proposed obligations, not existing declarations. The correctness
proofs of `det` and `detViaDivisor` project this shared result.

### One image

```lean
namespace Hex.Matrix

/-- The determinant of `A` reduced modulo `m`, computed by elimination.
Returns `some 0` when a pivot column is entirely zero, and `none` when
the column contains a nonzero entry but no unit, which for composite `m`
can happen without the matrix being singular. -/
def detMod? (A : Matrix (ZMod64 m) n n) : Option (ZMod64 m)
```

**The two failure branches are different and both are needed.** A pivot
column that is entirely zero proves the determinant is zero modulo `m`,
which is a perfectly good residue to fold in: the transformed matrix has
a zero column, so its determinant is `0`, and the accumulated row
operations are determinant-preserving. Only a column with a nonzero
nonunit gives `none`. Collapsing the two makes `det` on the zero matrix
skip every modulus and never terminate, and it is the kind of mistake
that no oracle fixture catches because the answer is right whenever the
function returns.

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
/-- The determinant by Chinese remaindering, or `none` when the supply of
moduli runs out before the bound is reached. -/
def detModular? (A : Matrix Int n n) (fuel : Nat) : Option Int

theorem detModular?_eq [LawfulDetBound] (h : detModular? A fuel = some d) :
    d = Matrix.det A
```

The total wrapper is in `Hex.ModularMatrix`:

```lean
namespace Hex.ModularMatrix

/-- The determinant. Falls back to `Hex.Matrix.bareiss` when the modular
route does not finish. -/
def det (A : Hex.Matrix Int n n) : Int

theorem det_eq [Hex.Matrix.LawfulDetBound] (A : Hex.Matrix Int n n) :
    det A = Hex.Matrix.det A

end Hex.ModularMatrix
```

The loop folds one image per modulus into a `Crt` and stops when the
accumulated modulus exceeds `2 · hadamardBound A`, at which point
`crt_unique` identifies the symmetric representative with the answer.
Moduli at which `detMod?` returns `none` are skipped.

**The fallback is not defensive coding, it is the only way `det` is
total.** `ZMod64.Bounds` caps a modulus at `2^31`, so every allowed
modulus divides `L = lcm(1, …, 2^31 - 1)` and so does every product of
pairwise coprime allowed moduli. On the `1 x 1` matrix `[L]` the
determinant is `L`, the Hadamard bound is `L`, every image is zero, and
the accumulated modulus never exceeds `2L`. No amount of fuel helps.
[hex-modular](../../HexModular/SPEC/hex-modular.md) records the same obstruction for the
supply as a whole. Under design principle 8 the classification is neither
of the two fallback modes: `detModular?` propagates its `Option` upward,
and `det` is a dispatch between two complete algorithms rather than a
total form of a partial one.

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
namespace Hex.ModularMatrix

/-- The determinant, computed as a divisor found by lifting times a
cofactor found by Chinese remaindering. -/
def detViaDivisor (A : Hex.Matrix Int n n) (seed : Nat) : Int

end Hex.ModularMatrix
```

Three things make this rigorous rather than heuristic, and the middle one
is easy to get wrong:

- `d ∣ det A` needs Cramer's rule. From `A y = d b` with `A` nonsingular,
  `y_i / d = det(A_i) / det(A)`, so `det(A) · y_i = d · det(A_i)` for
  every `i`, so `d` divides `det(A) · gcd_i(y_i)`.
- **The pair must be reduced first.** The divisibility conclusion needs
  `gcd(gcd_i y_i, d) = 1`. Dixon's reconstruction returns a common
  denominator that need not be the least one
  ([hex-modular](../../HexModular/SPEC/hex-modular.md) says so explicitly under "Vectors with a
  common denominator"), so `detViaDivisor` divides `y` and `d` through by
  their common gcd before using `d`. Omitting that step gives a `d` that
  does not divide the determinant and a wrong answer with no symptom.
- The cofactor still needs a bound, and it has one: `|det A / d| ≤
  hadamardBound A / d`, from the same hypothesis as before, with floor
  division on the right. Nothing is assumed about how large `d` is. A
  small `d` costs moduli, never correctness.
- **The images are of the cofactor, not of the determinant**, so each one
  is `(det A mod m) · (d⁻¹ mod m)` and a modulus with `gcd(d, m) ≠ 1` has
  no such inverse. Those moduli are skipped, exactly as the ones where
  `detMod?` returns `none` are. An implementation that reconstructs
  `det A` and divides afterwards has not saved anything, since the point
  of the divisor is to shrink the modulus the reconstruction needs.

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
4. Reconstruct with `ratReconVec?` at bounds
   `P = max_i hadamardBound (A with column i replaced by b)` and
   `Q = hadamardBound A`. **The number of steps is set by
   `p^k > 2 P Q`**, from Cramer's rule: the `i`-th numerator is the
   determinant of `A` with column `i` replaced by `b`, and the common
   denominator divides `det A`. The maximum over `i` is not decoration.
   For `A = [[1, N], [0, 1]]` and `b = (0, 1)` the solution is `(-N, 1)`,
   while replacing the second column alone gives a bound of `1`, so a
   `P` read off one replaced column is wrong by a factor of `N`.
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
pivot product.

**Rational input, rational right-hand side.** A caller with `Rat` data
clears denominators. `solve?` does not accept `Rat`, because the
clearing is a scalar multiplication the caller can do exactly once, and
accepting `Rat` would invite it to be done per call.

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
| `detViaDivisor` | one solve plus `⌈log₂(H/d)/w⌉` images | `O(n³ + n² h)` typical | small |
| `solve?` | one inverse plus `k = O(h/w)` steps | `O(n³ + n² h / w)` | `O(n·h)` in the reconstruction |
| `rankCert?` | per attempt: modular reduction, `det B`, one decomposition and `r` solves | `O(n m + n m r + r³ + r³ k)` plus the determinant route, for `k` lifting digits per solve | determinant/reconstruction costs plus `checkRank` below |
| `Hex.Matrix.checkRank` | `B * adj`, `adj * P`, `C * U`, and scalar multiplication | none | `O(r³ + r² m + n r m + n m)` ring operations; operand sizes include the certificate |
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

**The modulus supply should move to hex-mod-arith.** `ZMod64.Modulus`,
the bundled `ZMod64.Prime`, and `ZMod64.primesBelow` belong beside `ZMod64`,
per [hex-modular §The supply](../../HexModular/SPEC/hex-modular.md). This library is their
main consumer, and it passes bare `Nat` moduli on to `crtLoop`.

**`zmod64FieldOfPrime` should move to hex-mod-arith.** Set out in
[hex-modular](../../HexModular/SPEC/hex-modular.md). Without it, `rankModP` forces a dependency
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
- **Solve**, with integral solutions and with large-denominator
  solutions.

**Comparators.** FLINT's `fmpz_mat_det` becomes `gating` here, and this
is the one classification change this SPEC makes to an existing
comparator relationship. hex-bareiss classifies it `informational`
because the algorithms differ; once this library implements the same
algorithm the comparison is like-for-like and the reason for the
exemption is gone. Two thresholds, written down in advance:

- **Against `Hex.Matrix.bareiss`**, on the shared tridiagonal fixture,
  `detViaDivisor` must be faster at `n = 512` by at least `4x`, and the
  crossover rung below which Bareiss wins is **measured rather than
  predicted**, then written into the dispatch and into this SPEC. An
  earlier draft required "faster at every rung `n ≥ 64`", which guesses
  the crossover in the same document that says it will not guess it.
- **Against FLINT `fmpz_mat.det`**, on the same fixture and using the
  same startup-adjusted ratio the existing report defines,
  `detViaDivisor` should be within `5x` at every eligible rung. `5x` is a
  plausible constant factor between Lean and tuned C over GMP once the
  algorithms agree, and it is a target rather than a proved-reachable
  number: it becomes the required threshold after the first
  implementation measures it, and until then a miss is a finding to
  investigate rather than a merge-blocking failure.

Stating it that way is deliberate. A required check whose number nobody
has measured is either vacuous or an accident waiting to block a correct
implementation, and this SPEC has no prototype behind either figure.

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
    Matrix.mulVec (e A) (fun i => (y[i] : ℚ) / d) = fun i => (b[i] : ℚ)

theorem kernel_independent (h : kernel? A fuel = some K) :
    LinearIndependent ℚ (fun j : Fin (m - K.cert.rank) => v j)
theorem kernel_span (h : kernel? A fuel = some K) :
    Submodule.span ℚ (Set.range (fun j : Fin (m - K.cert.rank) => v j)) =
      LinearMap.ker (Matrix.mulVecLin M)
```

`det_eq` is the only one that needs the instance. Getting from the
Mathlib-free `det_eq [LawfulDetBound]` to this unconditional statement is
the discharge plus hex-determinant-mathlib's existing agreement between
the executable `Matrix.det` and Mathlib's.

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

5. **Rank.** Import `Hex.Matrix.RankCert Int` and `Hex.Matrix.checkRank`;
   add `rankModP`, `rankCert?`, `rankCert?_check`, and `rankModular` using
   the reusable decomposition. Add `Kernel`, `kernel?`, annihilation and
   free-block facts; the companion reuses `checkRank_sound` and proves
   `kernel_independent` and `kernel_span`. This milestone requires the
   hex-rank certificate/profile producer and companion, and milestone 3's
   decomposition and repeated-solve design from #10178 to be specified
   and implemented first.

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
  Rank.lean         -- rankModP, rankCert?, rankCert?_check, rankModular (imports HexRank)
  Kernel.lean       -- Kernel, kernel?, annihilation and free-block facts
HexModularMatrix.lean
HexModularMatrixMathlib/
  Bound.lean        -- the LawfulDetBound instance
  Det.lean          -- det_eq, Decidable (A.det = 0)
  Rank.lean         -- rank_eq via HexRankMathlib, rankModular_eq, kernel_independent, kernel_span
  Solve.lean        -- solve_eq
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
          goal: faster than Hex.Matrix.bareiss by at least 4x at n = 512 on the shared tridiagonal fixture, with the FLINT ratio recorded and the 5x target reviewed after the first measurement
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
          description: square and rectangular matrices at several ranks, measuring rankCert? and rankModular
        - name: rank-bad-primes
          description: large-coefficient rank-deficient s L R matrices, with s the product of initial producer primes, requiring skips and a successful certificate
        - name: solve
          description: systems with integral and with large-denominator solutions
  HexModularMatrixMathlib:
    deps: [HexModularMatrix, HexRankMathlib, HexMatrixMathlib, HexDeterminantMathlib, HexRowReduceMathlib, HexModularMathlib]
    mathlib: true
    done_through: 0
    status: planned
```

`HexDeterminant` is a dependency for the row-operation determinant
lemmas, not for the Leibniz determinant, which nothing here calls.
`HexBareiss` supplies the total determinant fallback.
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
- **The determinant does not also produce a rank witness.** Its scalar
  result does not supply the selected minor and adjugate required by
  `Hex.Matrix.RankCert Int`; callers needing rank evidence use `rankCert?`
  (or hex-rank's total producer) separately.
- **The crossover with Bareiss.** The benchmark will show a size below
  which the fraction-free path is faster, and the dispatch should use it.
  This SPEC does not guess the number.
