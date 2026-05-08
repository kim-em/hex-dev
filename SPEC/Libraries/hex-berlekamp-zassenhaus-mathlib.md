# hex-berlekamp-zassenhaus-mathlib (depends on hex-berlekamp-zassenhaus + hex-poly-z-mathlib)

Instantiates the conditional correctness theorems from
hex-berlekamp-zassenhaus (which take an abstract coefficient bound)
with the Mignotte bound from hex-poly-z-mathlib, giving unconditional
results. All statements use the `Factorization` record from
`hex-berlekamp-zassenhaus.md`'s output-convention section:

```lean
theorem factor_product (f : ZPoly) :
    Factorization.product (factor f) = f

theorem factor_irreducible_of_nonUnit (f : ZPoly) :
    ∀ (g, m) ∈ (factor f).factors, Hex.ZPoly.Irreducible g

theorem factor_unique (f : ZPoly) (φ ψ : Factorization) :
    Factorization.product φ = f →
    Factorization.product ψ = f →
    (∀ (g, m) ∈ φ.factors, Hex.ZPoly.Irreducible g) →
    (∀ (g, m) ∈ ψ.factors, Hex.ZPoly.Irreducible g) →
    φ.scalar = ψ.scalar ∧
    φ.factors.toList.toFinmap = ψ.factors.toList.toFinmap
-- Multiset equality of polynomial factors with multiplicities; the
-- scalar matches because both Factorizations encode the same f.
-- Follows from `UniqueFactorizationMonoid.factors_unique` over `Int`
-- (in `Mathlib.RingTheory.UniqueFactorizationDomain.Basic`) via the
-- ring equivalence. `Polynomial ℤ` gets the
-- `UniqueFactorizationMonoid` instance from
-- `Mathlib.RingTheory.Polynomial.UniqueFactorization`.

theorem checkIrreducibleCert_sound
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate) :
    checkIrreducibleCert f cert = true → Irreducible f
```

`factor_irreducible_of_nonUnit` is the corrected form of the old
`factor_irreducible` (which incorrectly claimed *every* element of
the old `Array ZPoly` output was irreducible — false for content
factors like `[C 6, ...]` since `C 6 = C 2 · C 3` is reducible in
`Polynomial ℤ`). Under the new `Factorization` API, the
`factors` field by SPEC contains *only* irreducible non-unit
polynomial factors, so the per-element irreducibility claim is
precisely what we want.

**Bridge for `Hex.ZPoly.Irreducible`** (the Mathlib-free class
defined in `hex-berlekamp-zassenhaus.md`):

```lean
theorem Hex.ZPoly.Irreducible_iff_polynomialIrreducible (f : ZPoly) :
    Hex.ZPoly.Irreducible f ↔ Irreducible (toPolynomial f)
```

Cheap from the existing `irreducibleByFactorization_iff` infrastructure
plus the `Hex.ZPoly.IsUnit f ↔ IsUnit (toPolynomial f)` bridge from
`hex-poly-z-mathlib`. The two definitions of irreducibility (ours and
Mathlib's) are propositionally identical when phrased over the
respective unit predicates; the bridge unfolds both sides and
rewrites `IsUnit` and `(· * ·)` through `toPolynomial`.

Also connects to Mathlib's `Polynomial ℤ` and provides
`Decidable (Irreducible f)` for `f : Polynomial ℤ`.

This library is thin — the hard work is split between
hex-berlekamp-zassenhaus (algorithmic correctness, Mathlib-free) and
hex-poly-z-mathlib (the Mignotte bound).
