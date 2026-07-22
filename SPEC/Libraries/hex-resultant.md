# hex-resultant (polynomial resultant via subresultant chain, depends on hex-poly)

Polynomial resultant and discriminant for `Hex.DensePoly R` over a UFD
`R`. Computed via the **subresultant pseudo-remainder sequence**
(Collins 1967; Brown 1978), the standard fraction-free algorithm.

The main instantiations are `R = Int` (that is, `ZPoly`), `R = ZPoly`
for bivariate elimination, and `R = NumberTower.Elem T` for norms over
successive number-field extensions. The last consumer lives in
`hex-number-field-tower`; this library remains independent of it.

## Why subresultants, not Sylvester+Bareiss

A naive implementation could form the `(n+m) × (n+m)` Sylvester matrix
and take its Bareiss determinant. That costs `O((n+m)³)` coefficient
operations. The subresultant chain reaches the same value in at most
`min(n, m)` pseudo-division steps, `O(n·m)` coefficient operations
total. Intermediate coefficients in both algorithms are (up to sign)
minors of the Sylvester matrix, so both have the same well-controlled
coefficient growth: bit-length `O((n+m) · (log(n+m) + log ‖f‖∞ +
log ‖g‖∞))` over `R = Int`. The saving is the operation count, a
factor of roughly `n+m`.

It also keeps the dependency surface minimal. The algorithm is
iterated polynomial pseudo-division plus scale-factor bookkeeping.
Pseudo-division stays inside `R` and is defined in this library
(`HexPoly` has only Euclidean division, which needs `Div` on the
coefficients). No matrix dependency, depth 1.

## Contents

```lean
namespace Hex.DensePoly

/-- Polynomial pseudo-division: for `f, g : DensePoly R` with `g ≠ 0`
    and `g.degree? ≤ f.degree?`, returns `(quotient, pseudoRemainder)`
    where `lc(g)^(deg f - deg g + 1) · f = quotient * g + pseudoRemainder`
    and `pseudoRemainder.degree? < g.degree?`. Pre-multiplying by
    `lc(g)^(deg f − deg g + 1)` keeps all coefficients in `R`, so no
    coefficient division occurs. -/
def pseudoDivMod (f g : DensePoly R) : DensePoly R × DensePoly R := ...

/-- Subresultant pseudo-remainder sequence:
    `r₀ = f`, `r₁ = g`, and `r_{k+1}` is the pseudo-remainder of
    `r_{k-1}` by `r_k`, divided by the scale factor `β_k` (the division
    is exact). The sequence terminates when some `r_N = 0`. Requires
    `g.degree? ≤ f.degree?`; `resultant` handles the swap. -/
def subresultantChain (f g : DensePoly R) : Array (DensePoly R) := ...

/-- Resultant of `f` and `g`. When `f.degree? < g.degree?`, computed as
    `(-1)^(deg f · deg g) · resultant g f`. Returns `0` when the chain
    terminates with a final nonzero element of positive degree (that
    is, when `gcd(f, g)` has positive degree, which over the algebraic
    closure of the fraction field means `f` and `g` share a common
    root). Otherwise returns the constant `r_{N-1}` corrected by the
    accumulated scale factors and signs from the chain. -/
def resultant (f g : DensePoly R) : R := ...

/-- Discriminant, by the standard formula
    `disc f = (-1)^(n·(n-1)/2) · resultant f f.derivative / lc(f)`
    where `n = deg f`. For nonzero `f` the division is exact, since
    `lc(f)` divides `resultant f f.derivative`. -/
def disc (f : DensePoly R) : R := ...

end Hex.DensePoly
```

The implementation works for any commutative ring `R` with
multiplicative cancellation (a UFD suffices). `DensePoly R` itself
needs `[Zero R] [DecidableEq R]` plus the ring operations; both
`R = Int` and `R = ZPoly` qualify.

## Algorithm exposition

The subresultant chain construction (Collins 1967, in Brown's 1978
formulation):

- Start with `r₀ = f`, `r₁ = g`. Track auxiliary scale factors
  `β_k` and `ψ_k` per the standard recurrence. These absorb the
  pseudo-division blow-up, so intermediate coefficients stay
  polynomial-size in the input.
- At each step: pseudo-divide `r_{k-1}` by `r_k` to get a remainder,
  then divide it exactly by `β_k` (a specific product of leading
  coefficients of `r_k` and earlier `ψ` values) to get `r_{k+1}`.
- Continue until `r_N = 0`.

The resultant is then:

- `0` if the last nonzero element `r_{N-1}` has positive degree (`f`
  and `g` share a common root);
- otherwise, the constant `r_{N-1}` scaled by a specific power of
  `ψ_{N-1}` and a sign determined by the degree sequence of the chain.

The exact recurrences for `β_k`, `ψ_k`, and the final correction are
standard textbook material. Follow Geddes-Czapor-Labahn ch. 7
(Algorithm 7.3 and the surrounding discussion), which spells out all
of the bookkeeping; von zur Gathen and Gerhard ch. 6 covers the same
ground.

## File organisation

- `HexResultant/Basic.lean`: `pseudoDivMod`, `subresultantChain`,
  `resultant`, and their basic computational properties (chain
  termination, degree bounds).
- `HexResultant/Discriminant.lean`: `disc` and the algebraic
  identities we need downstream (for example
  `disc (f * g) = disc f · disc g · (resultant f g)²`).
- `conformance/HexResultant/Conformance.lean` and
  `conformance/HexResultant/EmitFixtures.lean`: conformance driver and
  fixture emission, in the shared `conformance/` sub-project.
- `bench/HexResultant/Bench.lean`: bench driver, in the shared
  `bench/` sub-project. Benches time `resultant` and `disc` on
  committed fixture families of increasing degree. They are
  Mathlib-free, per [SPEC/benchmarking.md](../benchmarking.md); there
  is nothing to compare against in-process, since Mathlib's
  `Polynomial.resultant` is noncomputable. Cross-checking values
  against external systems happens in the conformance oracle, not in
  the bench.

## Conformance fixtures

Per [SPEC/testing.md](../testing.md), fixtures are tiered into
`core` / `ci` / `local`:

- *core* (Lean-only):
  - `resultant (X − a) (X − b) = a − b` for small integer `a, b`.
  - `resultant f 1 = 1` for any `f`.
  - `resultant (X² + 1) (X − 1) = 2`, plus a few small
    quadratic-times-linear cases.
  - `disc (X² + b·X + c) = b² − 4·c` for small `b, c`.
  - Common-root cases: `resultant (X − 1) (X² − 1) = 0`,
    `resultant (X² + 1) (X² + 1) = 0`.
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
- `subresultantChain f g` has at most `min(n, m) + 1` elements, hence
  `O(min(n, m))` pseudo-division steps and `O(n·m)` coefficient
  operations total. Over `R = Int`, intermediate coefficients have
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
- Brown, W. S. *The subresultant PRS algorithm.* ACM TOMS 4 (1978),
  237-249. The standard reference for the modern formulation.
- Geddes, K. O.; Czapor, S. R.; Labahn, G. *Algorithms for Computer
  Algebra.* Kluwer, 1992. Chapter 7 is a clean textbook treatment
  with all the scale-factor bookkeeping spelt out.
- von zur Gathen, J.; Gerhard, J. *Modern Computer Algebra.* CUP, 3rd
  ed. 2013. Chapter 6.
