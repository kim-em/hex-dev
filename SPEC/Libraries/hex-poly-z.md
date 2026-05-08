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
- Gauss's lemma (`content(f * g) = content(f) * content(g)`) is not
  needed in this library — it transfers from Mathlib via the ring
  equivalence in hex-poly-z-mathlib.
