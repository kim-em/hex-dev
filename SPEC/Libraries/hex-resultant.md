# hex-resultant (polynomial resultant via subresultant chain, depends on hex-poly)

Polynomial resultant and discriminant for `Hex.DensePoly R` over a UFD
`R` (in particular `ZPoly = DensePoly Int`). Computed via the
**subresultant pseudo-remainder sequence** (Brown 1971; Collins 1967),
the standard fraction-free algorithm.

## Why subresultants, not Sylvester+Bareiss

A naïve implementation could form the Sylvester matrix and take its
Bareiss determinant. This works mathematically but is the wrong
asymptotic regime: `O((n+m)³)` coefficient operations and a quadratic
blowup in intermediate coefficient bit-length. The subresultant chain
is `O(n·m)` polynomial-pseudodivision steps with provably-bounded
intermediate coefficient growth (the "fundamental theorem of
subresultants") — significantly faster on inputs of practical size.

It also keeps the dependency surface minimal: subresultants reduce to
iterated polynomial pseudo-division, which lives in `HexPoly` already.
No matrix dep, depth 1.

## Contents

```lean
namespace Hex.DensePoly

/-- Polynomial pseudo-division: for `f, g : DensePoly R` with
    `g.degree ≤ f.degree`, returns `(quotient, pseudoRemainder)` where
    `lc(g)^(deg f - deg g + 1) · f = quotient * g + pseudoRemainder`
    and `pseudoRemainder.degree < g.degree`. No division required:
    pre-multiplication by `lc(g)^(deg f − deg g + 1)` ensures all
    coefficients stay in `R`. -/
def pseudoDivMod (f g : DensePoly R) : DensePoly R × DensePoly R := ...

/-- Subresultant pseudo-remainder sequence:
    `r₀ = f`, `r₁ = g`, `r_{k+1} = pseudoRemainder` of (rescaled)
    `r_{k-1}` divided by `r_k`. The sequence terminates when some
    `r_N = 0`. -/
def subresultantChain (f g : DensePoly R) : Array (DensePoly R) := ...

/-- Resultant of `f` and `g`. Returns `0` when the chain terminates
    with a non-constant final non-zero element (i.e., when `gcd(f, g)`
    has positive degree, which over the algebraic closure means
    `f` and `g` share a common root); otherwise returns the appropriate
    leading coefficient with sign and scale corrections. -/
def resultant (f g : DensePoly R) : R := ...

/-- Discriminant. Standard formula:
    `disc f = (-1)^(n·(n-1)/2) · resultant f f.derivative / lc(f)`
    where the division is exact when `lc(f) ≠ 0` (since
    `lc(f) | resultant f f.derivative` for any nonzero `f`). -/
def disc (f : DensePoly R) : R := ...

end Hex.DensePoly
```

The implementation works for any commutative ring `R` with
multiplicative cancellation (UFD suffices); used in this project for
`R = Int` (via `ZPoly`).

## Algorithm exposition

The subresultant chain construction (Brown 1971, with Collins 1967's
later refinements):

- Start with `r₀ = f`, `r₁ = g`. Track auxiliary scale factors
  `β_k` and `ψ_k` per the standard recurrence (these absorb the
  pseudo-division blow-up so intermediate coefficients stay polynomial
  in the input size).
- At each step: pseudo-divide `r_{k-1}` by `r_k`, getting a remainder
  `r_{k+1}`. Rescale by the appropriate combination of leading
  coefficients of `r_k` and previous β's.
- Continue until `r_N = 0`.

The resultant is then:
- `0` if the chain terminates with the previous element `r_{N-1}` of
  positive degree (i.e., `f` and `g` share a common root);
- otherwise, a specific scaled leading coefficient of `r_{N-1}`
  (concretely: `ψ_{N-1}^(degree drop) · r_{N-1}.coeff 0` with sign
  corrections from the chain's history).

The exact scale-factor bookkeeping is standard textbook material
(Geddes-Czapor-Labahn ch. 7; von zur Gathen and Gerhard ch. 6).

## Layered file organisation

- `HexResultant/Basic.lean` — `pseudoDivMod`, `subresultantChain`,
  `resultant`, basic computational invariants (e.g., chain
  termination, `resultant f g = 0` detection).
- `HexResultant/Discriminant.lean` — `disc` and basic algebraic
  identities (e.g., `disc (f * g) = disc f · disc g · resultant f g²`,
  to the extent we need them downstream).
- `HexResultant/Conformance.lean` — `core` fixtures including small
  hand-checkable cases, well-known resultants (Chebyshev, cyclotomic
  pairs), and zero-on-shared-root cases.
- `HexResultant/Bench.lean` — performance benchmarks against
  Mathlib's noncomputable `Polynomial.resultant` (via small fixtures
  in `EmitFixtures`) or against an external CAS.
- `HexResultant/EmitFixtures.lean` — fixture emission for the
  conformance harness.

## Conformance fixtures

Per `SPEC/testing.md`, fixtures tiered into `core` / `ci` / `local`:

- *core* (Lean-only):
  - `resultant (X − a) (X − b) = a − b` for small integer `a, b`.
  - `resultant f 1 = 1` for any `f`.
  - `resultant (X² + 1) (X − 1) = 2`; cross-check on a few small
    quadratic-times-linear cases.
  - `disc (X² + b·X + c) = b² − 4·c` for small `b, c`.
  - Common-root cases: `resultant (X − 1) (X² − 1) = 0`,
    `resultant (X² + 1) (X² + 1) = 0`.
- *ci* (CI, with external oracle when available):
  - 30 random degree-10 pairs with deterministic seed; oracle from
    SageMath or python-flint.
- *local* (developer-driven):
  - High-degree resultants for performance-checking against the
    asymptotic claim.

External oracles: SageMath (`R.<x> = ZZ[]; (f).resultant(g)`),
python-flint (`fmpz_poly_q.resultant`).

## Complexity contract

- `pseudoDivMod` for `f, g` of degrees `n, m` runs in `O((n − m + 1) · m)`
  coefficient operations (roughly equivalent to schoolbook polynomial
  division).
- `subresultantChain f g` runs in `O(n · m)` polynomial-pseudodivision
  steps. Total coefficient operations: `O(n·m·max(n,m))` over a UFD,
  with intermediate coefficients of bit-length `O((n+m) · log
  ‖f, g‖∞)` (the subresultant theorem's bound).
- `resultant`, `disc`: dominated by the chain construction; same
  asymptotic.

This is asymptotically better than `O((n+m)³ · log² ‖f, g‖∞)` for the
Sylvester+Bareiss approach, by a factor of roughly `(n+m)`.

## References

- Brown, W. S. *The subresultant PRS algorithm.* ACM TOMS 4 (1978),
  237–249. The standard reference for the modern formulation.
- Collins, G. E. *Subresultants and reduced polynomial remainder
  sequences.* J. ACM 14 (1967), 128–142. The original.
- Geddes, K. O.; Czapor, S. R.; Labahn, G. *Algorithms for Computer
  Algebra.* Kluwer 1992. Chapter 7 has a clean modern textbook
  treatment with all the scale-factor bookkeeping spelt out.
- von zur Gathen, J.; Gerhard, J. *Modern Computer Algebra.* CUP, 3rd
  ed. 2013. Chapter 6.
