# hex-poly-z (polynomials over Z, depends on hex-poly)

Specialized polynomial arithmetic over `Z`.

**Contents:**
- `ZPoly` = `DensePoly Int`
- Polynomial congruence:
  ```lean
  def ZPoly.congr (f g : ZPoly) (m : Nat) : Prop :=
      ∀ i, (f.coeff i - g.coeff i) % m = 0

  def ZPoly.coprimeModP (f g : ZPoly) (p : Nat) : Prop := ...
  ```
- Content and primitive part: `f = content(f) * primitivePart(f)`
- Mignotte bound computation: `|gⱼ| ≤ C(k,j) · ‖f‖₂` for any degree-k
  factor `g | f` in `Z[x]`. The computation is just binomial coefficients
  and the 2-norm of `f`'s coefficients. The proof that the bound is valid
  lives in `hex-poly-z-mathlib`.

  **Complexity contract for the Mignotte computation.** Both bodies
  must be polynomial in their inputs:

  - `binom n k` uses the multiplicative formula
    `(∏ i<k, (n − i)) / k!` and runs in `O(k)` `Nat` multiplications.
    The Pascal-triangle recursion `binom (n+1) (k+1) = binom n k +
    binom n (k+1)` is forbidden as the executable body — without
    memoisation it takes `Θ(2^k)` calls and a Mignotte computation
    over a degree-50 factor cannot terminate.
  - `floorSqrt n` runs in `O(log n)` iterations via Newton's method
    `x ← (x + n / x) / 2` (or bit-by-bit binary search). Descending
    linear search is forbidden: `coeffNormSq f` for any non-trivial
    `ZPoly` is at least `2^40`, and a linear-time `floorSqrt` makes
    `coeffNorm f` non-terminating in practice.

  Both prohibitions are instances of [PLAN/Phase1.md](../../PLAN/Phase1.md)'s
  general "no alternative implementations with the wrong algorithmic
  complexity" rule; they are spelt out here because the SPEC's
  one-line description "binomial coefficients and the 2-norm" is
  satisfied by both correct and wrong-complexity bodies.

**Key properties:**
- `primitivePart(f)` is primitive (content = 1)
- Gauss-style corollaries needed for downstream Mathlib-free
  factorization live in this library. The general statement
  `content(f * g) = content(f) * content(g)` still transfers from
  Mathlib via the ring equivalence in hex-poly-z-mathlib, but the
  Berlekamp–Zassenhaus Z-level reassembly path needs (at least) the
  following primitive-product corollary directly here so its proof
  stays Mathlib-free:
  - `Primitive p → Primitive q → Primitive (p * q)` (used to discharge
    `primitiveSquareFreeDecomposition_squareFreeCore_repeatedPart_primitive`).
  - The associated rational-associate cancellation
    (`rational_associate_primitive_unit`): if two primitive nonzero
    `ZPoly`s agree as rational associates with rational factor `u`,
    then `u = ±1`.
  - The signed integer reassembly
    (`primitiveSquareFreeDecomposition_reassembly_signed`) for the
    BZ Z-level recombination chain.

**Units in `ℤ[x]`:**

```lean
/-- A ZPoly is a unit iff it equals ±1 as a constant polynomial.
    Coefficient-ring-specific (units in `R[x]` depend on units in
    `R`), so this lives in `HexPolyZ` rather than the generic
    `HexPoly`. -/
def Hex.ZPoly.IsUnit (f : ZPoly) : Prop := f = .C 1 ∨ f = .C (-1)

instance : Decidable (Hex.ZPoly.IsUnit f) := …   -- structural via DecidableEq
```

Used by downstream irreducibility predicates (in
`hex-berlekamp-zassenhaus`) and by any code that needs to test
unit-ness in `ℤ[x]`. The Mathlib bridge
`Hex.ZPoly.IsUnit f ↔ IsUnit (toPolynomial f)` lives in
`hex-poly-z-mathlib`.

## External comparators

| Comparator | Class | Scope |
|---|---|---|
| FLINT `fmpz_poly` via python-flint | informational | bench targets exercising arithmetic on `ZPoly` (the integer-polynomial surface inherited from `HexPoly`) |

Same comparator and rationale as `hex-poly` (informational because
of FLINT's tuned Karatsuba/Toom-Cook/FFT crossovers vs Hex's
schoolbook + Karatsuba implementation). The Mignotte / Hensel-lift
data surfaces specific to `hex-poly-z` have no direct FLINT
analog at the same level of abstraction; those bench targets
declare absence with the `no-comparable-surface-in-named-comparator`
reason per `SPEC/benchmarking.md §"Comparator naming"`.

Structured metadata in `libraries.yml: HexPolyZ.phase4.comparators`.
