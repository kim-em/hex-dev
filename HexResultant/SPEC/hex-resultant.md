# hex-resultant (polynomial resultant via subresultant chain, depends on hex-poly)

Polynomial resultant and discriminant for `Hex.DensePoly R` over a
commutative exact-division domain. Computed via the **subresultant
pseudo-remainder sequence** (Collins 1967; Brown 1978), the standard
fraction-free algorithm.

The main instantiations are `R = Int` (that is, `ZPoly`), `R = ZPoly`
for bivariate elimination, and `R = NumberTower.Elem T` for norms over
successive number-field extensions. The last consumer lives in
`hex-number-field-tower`; this library remains independent of it.

## Why subresultants, not Sylvester+Bareiss

A naive implementation could form the `(n+m) × (n+m)` Sylvester matrix
and take its Bareiss determinant. That costs `O((n+m)³)` coefficient
operations. The subresultant chain reaches the same value in at most
`min(n, m) + 1` pseudo-division calls, `O(n·m)` coefficient operations
total. Intermediate coefficients in both algorithms are (up to sign)
minors of the Sylvester matrix, so both have the same well-controlled
coefficient growth: bit-length `O((n+m) · (log(n+m) + log ‖f‖∞ +
log ‖g‖∞))` over `R = Int`. The saving is the operation count, a
factor of roughly `n+m`.

It also keeps the dependency surface minimal. The algorithm is
iterated polynomial pseudo-division plus scale-factor bookkeeping.
Pseudo-division stays inside `R` and is defined in this library
(`HexPoly` has only Euclidean division, which needs `Div` on the
coefficients). Exact scalar quotients reuse that `Div` operation behind
the law package below. No matrix dependency, depth 1.

## Contents

```lean
namespace Hex

universe u

/-- Law required of the coefficient quotient used by Brown's exact divisions.
    It also implies cancellation by every nonzero right factor. -/
class ExactDivLaws (R : Type u) [Zero R] [Mul R] [Div R] : Prop where
  mul_div_cancel_right : ∀ a b : R, b ≠ 0 → (a * b) / b = a

variable {R : Type u}

/-- Total exact quotient wrapper. A zero denominator returns zero; on a
    nonzero exact division this is the underlying lawful quotient. -/
def exactDiv [Zero R] [DecidableEq R] [Div R] (a b : R) : R :=
  if b = 0 then 0 else a / b

/-- Natural powers by binary exponentiation, using only the executable `One`
    and `Mul` operations. -/
def powNat [One R] [Mul R] (x : R) (n : Nat) : R :=
  if n = 0 then 1 else
    let y := powNat (x * x) (n / 2)
    if n % 2 = 0 then y else y * x

/-- Brown's scalar update `x^n / y^(n-1)`, through `exactDiv`. -/
def divExp [Zero R] [DecidableEq R] [One R] [Mul R] [Div R]
    (x y : R) (n : Nat) : R :=
  exactDiv (powNat x n) (powNat y (n - 1))

namespace SubresultantMinor

/-- Proof-only square coefficient family. -/
abbrev Square (R : Type u) (n : Nat) := Fin n → Fin n → R

/-- Local first-row Laplace determinant. -/
def det [Zero R] [One R] [Add R] [Sub R] [Mul R] :
    {n : Nat} → Square R n → R := ...

end SubresultantMinor

namespace DensePoly

/-- Divide every coefficient by the same scalar through `exactDiv`. -/
noncomputable def divScalar [Zero R] [DecidableEq R] [Div R]
    (p : DensePoly R) (b : R) : DensePoly R :=
  if b = 0 then 0 else ofCoeffs (p.toList.map (fun a => a / b)).toArray

namespace Subresultant

/-- Default formal degree, with zero and constants both at degree zero. -/
def formalDegree [Zero R] [DecidableEq R] (p : DensePoly R) : Nat :=
  p.size - 1

/-- Scalar determinant giving coefficient `l` of subresultant index `J`. -/
def coeffMinor [Zero R] [DecidableEq R] [One R] [Add R] [Sub R] [Mul R]
    (J l : Nat) (f g : DensePoly R) : R := ...

/-- Generalized Sylvester subresultant of index `J`. -/
def poly [Zero R] [DecidableEq R] [One R] [Add R] [Sub R] [Mul R]
    (J : Nat) (f g : DensePoly R) : DensePoly R := ...

end Subresultant

/-- Polynomial pseudo-division: for `f, g : DensePoly R` with `g ≠ 0`
    and `g.degree? ≤ f.degree?`, returns `(quotient, pseudoRemainder)`
    where `lc(g)^(deg f - deg g + 1) · f = quotient * g + pseudoRemainder`
    and `pseudoRemainder.degree? < g.degree?`. Pre-multiplying by
    `lc(g)^(deg f − deg g + 1)` keeps all coefficients in `R`, so no
    coefficient division occurs. -/
def pseudoDivMod [Zero R] [DecidableEq R] [One R] [Add R] [Sub R] [Mul R]
    (f g : DensePoly R) : DensePoly R × DensePoly R := ...

/- The operation is total. Its two out-of-contract branches are stable public
   behavior: `pseudoDivMod f 0 = (0, f)`, and if nonzero `g` has larger degree
   than `f`, then `pseudoDivMod f g = (0, f)`. Both have corresponding rewrite
   lemmas. -/

/-- Brown's nonzero subresultant pseudo-remainder sequence. For two nonzero
    inputs it orders them by decreasing degree, stores both ordered inputs,
    and stops before the generated terminal zero. Zero inputs are omitted. -/
def subresultantChain [Zero R] [DecidableEq R] [One R] [Add R] [Sub R]
    [Mul R] [Div R] (f g : DensePoly R) : Array (DensePoly R) := ...

/-- Resultant with Mathlib's default-formal-degree conventions. For ordered
    nonzero inputs the Brown worker returns `(chain, hFinal)`; the value is
    `hFinal` exactly when the last chain element is constant and zero
    otherwise. Reversed inputs receive the standard degree-product sign. -/
def resultant [Zero R] [DecidableEq R] [One R] [Add R] [Sub R] [Mul R]
    [Div R] (f g : DensePoly R) : R := ...

/-- Standard discriminant. It is `1` for zero and constant polynomials. For
    positive degree `n`, let `d = f.derivative` and
    `gap = n - 1 - d.degree?.getD 0`. It is
    `(-1)^(n·(n-1)/2) ·
      exactDiv ((lc f)^gap · resultant f d) (lc f)`.
    The leading-coefficient power promotes the default-degree executable
    resultant to derivative formal degree `n - 1`; the quotient is exact. -/
def disc [Zero R] [DecidableEq R] [One R] [Add R] [Sub R] [Mul R]
    [Div R] [NatCast R] (f : DensePoly R) : R := ...

end DensePoly
end Hex
```

The executable definitions require only the operations they call: in
particular `[Div R]`, but not `ExactDivLaws R`. Correctness theorems require
`Lean.Grind.CommRing R`, decidable equality, and `ExactDivLaws R`. The law
implies nonzero-product and right-cancellation facts by applying `/ b` to an
equality with `b ≠ 0`.

`Int` supplies the law via `Int.mul_ediv_cancel`. There is a recursive
instance for `DensePoly R` whenever `R` has the law, so `ZPoly = DensePoly
Int` supports bivariate elimination, including nonunit constant and nonmonic
polynomial divisors. A future `NumberTower.Elem T` uses its existing `/`; its
Mathlib adjunct supplies the law once it installs the field laws. The tower's
computational core therefore remains law-free.

## Exact-division totality

`exactDiv a 0 = 0`. For nonzero denominators it is definitionally `a / b`;
`ExactDivLaws.mul_div_cancel_right` is the only quotient law used by the
correctness development. `divExp` and `divScalar` inherit the same zero branch.
A valid Brown run proves every denominator nonzero and every quotient exact.
On an invalid coefficient implementation or unreachable junk state, the
executable value remains deterministic but carries no algebraic claim.

## Certified pseudo-remainder algebra

For an ordered nonzero pair, reconstruction together with the strict
remainder-size bound uniquely determines `pseudoDivMod`. The public
`pseudoDivMod_unique` theorem packages that characterization; it lets the
correctness development reason from the algebraic contract instead of the
array folds implementing the quotient and remainder.

The same API proves the two homogeneity laws used in polynomial remainder
sequence arguments. For nonzero `a` and an ordered nonzero pair
(`g ≠ 0`, `g.size ≤ f.size`), if `d = f.size - g.size + 1`, then

```text
pseudoDivMod (a·f) g = (a·q, a·r)
pseudoDivMod f (a·g) = (a^(d-1)·q, a^d·r)
```

where `(q,r) = pseudoDivMod f g`. Nonzero scaling preserves dense size and
leading coefficients scale by `a`; those facts are exposed separately as
`size_scale` and `leadingCoeff_scale` under `[Div S] [ExactDivLaws S]`, whose
no-zero-divisor consequence is exactly what makes size preservation valid.

In the Mathlib adjunct, `PseudoDivMod.resultant_step` transports one reconstructed
pseudo-division step through the formal-degree Sylvester determinant. It
combines scalar homogeneity, the resultant row operation, and the swap sign.
This is the value recurrence needed by Brown correctness. It deliberately does
not claim the later coefficientwise exact divisions: their integrality is the
separate Brown--Traub subresultant theorem recorded by `BrownLaw`.
In particular, reversing `divScalar` by scaling requires the coefficientwise
exactness certified by that law; the homogeneity API does not assume it.

## Fraction-field proof bridge

The Brown--Traub integrality proof works first in a Mathlib-free fraction
field constructed locally from cross-multiplication classes. This is proof
infrastructure only: the executable recurrence never constructs a fraction,
and `hex-resultant` still has no matrix or Mathlib dependency. A nonzero Brown
input supplies the local `1 ≠ 0` witness needed by the coefficient embedding;
`ExactDivLaws` supplies cancellation and rules out zero products.

The generalized Sylvester constructions in this proof are local,
coefficient-indexed proof objects with their finite-sum identities developed
inside `hex-resultant`; they are not matrices from `hex-matrix` or
`hex-determinant`. Consequently the released dependency graph remains the one
stated at the top of this SPEC.

Concretely, `DensePoly.Subresultant.coeffMatrixAt` is a finite scalar
coefficient family at explicit formal degrees, and
`DensePoly.Subresultant.coeffMinor` takes its local first-row Laplace
determinant. `DensePoly.Subresultant.poly J f g` assembles the coefficient
minors for indices `0, …, J`, so its dense degree is at most `J`.  Keeping the
formal degrees explicit in the matrix core avoids dependent casts when the
coefficient ring changes.  The construction is total through truncated
natural subtraction; Brown identities use the meaningful range
`J ≤ min (formalDegree f) (formalDegree g)`. The proof route derives the
needed multilinearity, adjacent swaps, arbitrary duplicate-column vanishing,
adjacent-transposition sequence parity, column updates, and block identities
locally from the Laplace recursion rather than importing the matrix or
determinant libraries. The theorems `coeffMinor_map`, `poly_map`, and
`exists_coeff` prove that coefficient embedding commutes with the construction
and that every mapped minor coefficient has a base-ring image witness.
The theorems `poly_scale_left` and `poly_scale_right` establish the first
Brown--Traub transformation law: scaling an input contributes one scalar for
each column in that input's generalized Sylvester block. The concrete
`rotateBlocks` transformation moves two consecutive coefficient blocks using
adjacent swaps and proves the determinant factor
`(-1)^(left * right)`. Applied to the generalized Sylvester family,
`poly_swap` gives
`S_J(f, g) = (-1)^((deg f - J) * (deg g - J)) S_J(g, f)` without importing a
matrix or determinant library.

The next Brown--Traub transformation is also internal to this local
determinant. `SubresultantMinor.productCols` realizes the required unit
upper-triangular operation by adding multiplier-weighted `G` columns to the
later `F` columns; all sources stay strictly to the left of the destination
block, and `det_productCols` proves determinant preservation. For
`H = F + B * G` with `deg F = deg B + deg G`, `productCols_addMul` identifies
the transformed swapped matrix with the existing
`coeffMatrixAt (deg G) (deg F) J l G H`. Its explicit second formal degree keeps
`F`'s degree even when `H` drops. The coefficient identity `coeffFold_eq_mul`
includes negative and out-of-range indices, so the special coefficient row and
every ordinary Sylvester row use the same proof. Consequently
`coeffMinorAt_addMul` proves the column-operation form of Brown--Traub equation
(18): the original minor is the `G, H` minor times only the usual block-swap
sign. Collapsing the retained formal degree of `H` and producing the
leading-coefficient power is the next transformation.

The injective coefficient map extends to dense polynomials and preserves
normalized size, leading coefficients, constants, addition, subtraction,
scaling, multiplication, and ordered pseudo-division. Generalized Sylvester
subresultants can therefore establish the Brown scale identities in the
fraction field. Once a scalar or coefficientwise quotient is shown to lie in
the embedding image, `Fraction.divExp_exact` and
`DensePoly.Fraction.divScalar_exact` prove exactly the two reconstruction
equalities recorded by `BrownLaw`; the corresponding pullback lemmas identify
the quotient returned by the original coefficient ring. Thus the
fraction-field argument proves integrality instead of changing the executable
algorithm's coefficient type.

## Ordered Brown run

For nonzero `G₁, G₂` with `deg G₁ ≥ deg G₂`, write `nᵢ = deg Gᵢ`,
`gᵢ = lc(Gᵢ)`, and `prem A B = (pseudoDivMod A B).2`. The internal
worker returns the pair `(chain, hFinal)`. It initializes

```text
δ₁ := n₁ - n₂
h₂ := powNat g₂ δ₁
p := prem G₁ G₂

if p = 0:
  return (#[G₁, G₂], h₂)

G₃ := scale ((-1)^(δ₁ + 1)) p
state := (#[G₁, G₂, G₃], G₂, G₃, h₂)
```

Each loop state contains nonzero adjacent terms `prev = Gᵢ₋₁`, `curr =
Gᵢ`, and `hPrev = hᵢ₋₁`. One step is exactly

```text
δ := deg prev - deg curr
hCurr := divExp (lc curr) hPrev δ
p := prem prev curr

if p = 0:
  return (chain, hCurr)

divisor := (-1)^(δ + 1) * lc(prev) * powNat hPrev δ
next := divScalar p divisor

continue with (chain.push next, curr, next, hCurr)
```

Thus `hCurr = lc(curr)^δ / hPrev^(δ-1)`, and `next` is the
coefficientwise exact quotient of `prem prev curr` by
`(-1)^(δ+1) * lc(prev) * hPrev^δ`. Both divisions are exact and their
denominators are nonzero over an exact-division domain. These signs and powers
are part of the API contract; there is no later unpinned correction.

The executable recurrence calls the proved runtime twins `scaleImpl` and
`divScalarImpl`; `@[csimp]` correspondence theorems identify them with the
list-facing specifications above. Its two fuel/junk exits are deterministic:
fuel exhaustion returns the current `(chain, hPrev)`, while an unexpectedly
zero `next` returns `(chain, hCurr)` without storing that zero. Neither branch
is reachable from a valid ordered nonzero state over an exact-division domain;
`subresultantOrdered_brownLaw` is the proof boundary for that algebraic claim.
The structural guarantees below do not depend on it.

The public chain stores exactly Brown's nonzero `G₁, …, Gₖ`. It does not
store the generated terminal zero, gap zeros from defective subresultants, the
auxiliary `Hᵢ`, or the scalars `hᵢ`. Termination means
`prem Gₖ₋₁ Gₖ = 0`.

The structural API certifies this representation independently of the value
correspondence: every stored term is nonzero, adjacent sizes strictly decrease
after the first two entries, and the chain length is at most
`min(deg f, deg g) + 2` for nonzero inputs. The worker's public
`g.size + 1` budget is stable: adding arbitrary extra fuel does not change an
ordered run. These facts follow from the explicit zero guards together with the
pseudo-remainder bound and the fact that coefficientwise scaling and division
cannot increase dense size.

### Defective degree drops

Degrees strictly decrease after `G₂`. A drop `δ > 1` is retained as one
step. The new `Gᵢ` is the subresultant at the previous degree minus one even
when its actual degree is lower. Subresultants at the intervening degrees are
zero; the lower endpoint `Hᵢ` is a scalar multiple of `Gᵢ`, with leading
coefficient `hᵢ`. None of those implicit values is inserted into the public
chain, but `hᵢ` remains in the worker state because it determines both the
next exact divisor and the final resultant.

### Terminal value and input order

For an ordered nonzero run ending in `(#[G₁, …, Gₖ], hₖ)`, the resultant
is `hₖ` if `Gₖ` has degree zero and `0` otherwise. In particular, a final
constant `Gₖ` need not itself equal the resultant. For reversed nonzero
inputs,

```text
resultant f g = (-1)^(deg f * deg g) * resultantOrdered g f.
```

Equivalently, the swap negates exactly when both degrees are odd.
Equal-degree inputs retain caller order; only a strict degree reversal swaps
the arguments, so the tie case does not acquire an extra sign.

The total chain wrapper omits zero inputs:

```text
subresultantChain 0 0 = #[]
subresultantChain f 0 = #[f]    when f ≠ 0
subresultantChain 0 g = #[g]    when g ≠ 0
```

For two reversed nonzero inputs it starts with the degree-ordered pair. The
resultant handles zero inputs before the run, using default formal degrees:

```text
resultant f 0 = if f.size ≤ 1 then 1 else 0
resultant 0 g = if g.size ≤ 1 then 1 else 0
resultant (C a) (C b) = 1
resultant f (C c) = c ^ (f.degree?.getD 0)
resultant (C c) g = c ^ (g.degree?.getD 0)
```

Consequently `resultant 0 0 = 1`. These conventions agree with the pinned
Mathlib determinant resultant and its `0^0 = 1` behavior.

Finally, `disc f = 1` whenever `f.size ≤ 1`. For positive degree `n`, let
`d = f.derivative` and `gap = n - 1 - d.degree?.getD 0`. The default-degree
resultant is promoted to derivative formal degree `n - 1` by
`powNat f.leadingCoeff gap * resultant f d` before taking the signed exact
quotient by `lc(f)`. This correction is essential in positive characteristic,
where the derivative's actual degree can fall below `n - 1`; with it the
quotient is exact over every stated exact-division domain.

## File organisation

- `HexResultant/ExactDiv.lean`: `ExactDivLaws`, the total exact-division
  wrappers, and the `Int`, field, and recursive dense-polynomial instances.
- `HexResultant/Basic.lean`: `pseudoDivMod` and its computational properties.
- `HexResultant/PseudoDivMod.lean`: uniqueness, nonzero scaling, and the
  left/right pseudo-division homogeneity laws.
- `HexResultant/Fraction.lean`: the proof-only Mathlib-free fraction field,
  injective coefficient embedding, and exact scalar quotient pullback.
- `HexResultant/FractionPoly.lean`: the injective dense-polynomial embedding,
  its algebraic and pseudo-division transport laws, and coefficientwise
  quotient pullback.
- `HexResultant/SubresultantMinor.lean`: the local coefficient-indexed
  Sylvester determinant, generalized subresultant polynomials, and their
  fraction-embedding image certificates.
- `HexResultant/DeterminantAlgebra.lean`: local column multilinearity,
  adjacent swaps and swap-sequence parity, arbitrary alternation and update
  laws, consecutive-block scaling, and the resulting left/right homogeneity
  laws for generalized subresultants.
- `HexResultant/BlockDeterminant.lean`: dimension recasting, numeric adjacent
  swaps, consecutive-block rotation with its parity law, and the resulting
  generalized-subresultant input-swap law.
- `HexResultant/BrownTraub.lean`: multiplier-convolution column updates, the
  resulting `G, H` coefficient matrix, and the signed column-operation identity
  of Brown--Traub equation (18).
- `HexResultant/Subresultant.lean`: the Brown worker,
  `subresultantChain`, `resultant`, chain termination, and degree bounds.
- `HexResultant/Discriminant.lean`: `disc` and the algebraic
  identities we need downstream (for example
  `disc (f * g) = disc f · disc g · (resultant f g)²`).
- `conformance/HexResultant/Conformance.lean` and
  `conformance/HexResultant/EmitFixtures.lean`: conformance driver and
  fixture emission, in the shared `conformance/` sub-project.
- `bench/HexResultant/Bench.lean`: bench driver, in the shared
  `bench/` sub-project. Benches time `pseudoDivMod`, `subresultantChain`,
  `resultant`, and `disc` on committed fixture families of increasing degree.
  They are Mathlib-free, per
  [SPEC/benchmarking.md](../../SPEC/benchmarking.md). Mathlib's
  `Polynomial.resultant` is noncomputable, so it is not an in-process
  comparator. FLINT does provide a separately timed comparable
  resultant/discriminant surface for the Phase-4 report; exact value
  cross-checking against FLINT and PARI remains in the conformance oracle.

## Conformance fixtures

Per [SPEC/testing.md](../../SPEC/testing.md), fixtures are tiered into
`core` / `ci` / `local`:

- *core* (Lean-only):
  - `resultant (X − a) (X − b) = a − b` for small integer `a, b`.
  - `resultant f 1 = 1` for any `f`.
  - `resultant (X² + 1) (X − 1) = 2`, plus a few small
    quadratic-times-linear cases.
  - Total conventions: `resultant 0 0 = 1`, two constants give `1`,
    and a positive-degree polynomial paired with zero gives `0`.
  - `disc (X² + b·X + c) = b² − 4·c` for small `b, c`.
  - `disc 0 = 1` and `disc (C c) = 1`, including nonunit `c`.
  - Common-root cases: `resultant (X − 1) (X² − 1) = 0`,
    `resultant (X² + 1) (X² + 1) = 0`.
  - The defective-drop examples `G₁ = 2X⁴+2X³+X+2`,
    `G₂ = 2X³+1`, whose final chain constant is `4` but resultant is
    `16`, and `G₁ = -X⁴`, `G₂ = 2X³-1`, which exercises both
    nonunit exact divisions and has resultant `-1`.
  - Small generalized-minor pins cover both Sylvester blocks, a repeated-row
    zero above index `J`, degree reversal, equal degrees, regular and defective
    Brown-chain terms, left/right homogeneity, and a bivariate `ZPoly`
    coefficient ring. Direct local-determinant checks cover adjacent swaps,
    swap-sequence parity and action, arbitrary duplicate columns, and arbitrary
    column updates. An equal-degree `H = F + B * G` pin with `J > 0`, odd swap
    parity, and `deg H < deg G` checks the multiplier transformation entrywise
    and then checks equation (18). The local Laplace determinant is factorial
    proof infrastructure, so these checks stay deliberately small rather than
    joining the random degree-10 resultant sweep.
  - A bivariate case over `R = ZPoly`, exercising the
    `hex-number-field` instantiation: for example
    `resultant_y (y² − t) (y − t) = t² − t`.
- *ci* (CI, with external oracle when available):
  - 30 random degree-10 pairs with a deterministic seed; oracle from
    python-flint, with cypari2 as a secondary implementation.
- *local* (developer-driven):
  - High-degree resultants, timed against the complexity contract.

External oracles: python-flint (`fmpz_poly.resultant`) and cypari2
(`polresultant`). Sage is not used as an oracle.

## Complexity contract

- `pseudoDivMod` for `f, g` of degrees `n, m` runs in
  `O((n − m + 1) · m)` coefficient operations, the same as schoolbook
  polynomial division.
- For two nonzero inputs, `subresultantChain f g` stores at most
  `min(n, m) + 2` nonzero elements. It performs exactly one fewer
  pseudo-division calls than stored elements, including the final call whose
  zero result is not stored, hence at most `min(n, m) + 1` calls and
  `O(n·m)` coefficient operations total. Zero-input wrappers store at most
  one element and perform no pseudo-division. Over `R = Int`, intermediate coefficients have
  bit-length `O((n+m) · (log(n+m) + log ‖f‖∞ + log ‖g‖∞))`, since
  every chain element's coefficients are (up to sign) minors of the
  Sylvester matrix (the subresultant theorem) and Hadamard's bound
  applies.
- `resultant`, `disc`: dominated by the chain construction.

Sylvester+Bareiss costs `O((n+m)³)` coefficient operations on
intermediate values of the same bit-length, so the subresultant chain
is faster by a factor of roughly `n+m`.

## References

- Collins, G. E. *Subresultants and reduced polynomial remainder
  sequences.* J. ACM 14 (1967), 128-142. The original.
- Brown, W. S. [*The subresultant PRS algorithm*](https://people.eecs.berkeley.edu/~fateman/282/readings/brown.pdf).
  ACM TOMS 4 (1978), 237-249. Algorithm 1 is the recurrence pinned above.
- Eberl, M. [*Subresultants*](https://isa-afp.org/browser_info/current/AFP/Subresultants/Subresultant.html),
  Archive of Formal Proofs. Its verified `subresultant_prs` and
  `resultant_impl` are the executable reference for the state, signs, exact
  divisors, defective drops, and terminal convention.
- Geddes, K. O.; Czapor, S. R.; Labahn, G. *Algorithms for Computer
  Algebra.* Kluwer, 1992. Chapter 7 is a clean textbook treatment
  with all the scale-factor bookkeeping spelt out.
- von zur Gathen, J.; Gerhard, J. *Modern Computer Algebra.* CUP, 3rd
  ed. 2013. Chapter 6.
