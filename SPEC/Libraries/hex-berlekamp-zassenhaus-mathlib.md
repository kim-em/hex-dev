# hex-berlekamp-zassenhaus-mathlib (depends on hex-berlekamp-zassenhaus + hex-poly-z-mathlib)

Instantiates the conditional correctness theorems from
hex-berlekamp-zassenhaus (which take an abstract coefficient bound)
with the Mignotte bound from hex-poly-z-mathlib, giving unconditional
results:
```lean
theorem factor_product (f : ZPoly) :
    Array.foldl (· * ·) 1 (factor f) = f

theorem factor_irreducible (f : ZPoly) :
    ∀ g ∈ factor f, Irreducible g

-- Follows from Mathlib's `UniqueFactorizationMonoid.factors_unique`
-- (in `Mathlib.RingTheory.UniqueFactorizationDomain.Basic`) via the
-- ring equivalence. `Polynomial ℤ` gets the `UniqueFactorizationMonoid`
-- instance from `Mathlib.RingTheory.Polynomial.UniqueFactorization`.
theorem factor_unique (f : ZPoly) (gs hs : Array ZPoly) :
    Array.foldl (· * ·) 1 gs = f →
    Array.foldl (· * ·) 1 hs = f →
    (∀ g ∈ gs, Irreducible g) →
    (∀ h ∈ hs, Irreducible h) →
    gs.toList ~ hs.toList  -- multiset equality up to associates

theorem checkIrreducibleCert_sound
    (f : ZPoly) (cert : ZPolyIrreducibilityCertificate) :
    checkIrreducibleCert f cert = true → Irreducible f
```

Also connects to Mathlib's `Polynomial ℤ` and provides
`Decidable (Irreducible f)` for `f : Polynomial ℤ`.

**Bridge for `Hex.ZPoly.Irreducible`** (added alongside
`hex-berlekamp-zassenhaus`'s exposing the predicate as a class):

```lean
theorem Hex.ZPoly.Irreducible_iff_polynomialIrreducible (f : ZPoly) :
    Hex.ZPoly.Irreducible f ↔ Irreducible (toPolynomial f)
```

Cheap from the existing `irreducibleByFactorization_iff` infrastructure
plus the `Hex.ZPoly.IsUnit f ↔ IsUnit (toPolynomial f)` bridge from
`hex-poly-z-mathlib`. The two definitions of irreducibility (ours and
Mathlib's) are propositionally identical when phrased over the
respective unit predicates; the bridge is just unfolding both sides
and rewriting `IsUnit` and `(· * ·)` through `toPolynomial`.

This library is thin — the hard work is split between
hex-berlekamp-zassenhaus (algorithmic correctness, Mathlib-free) and
hex-poly-z-mathlib (the Mignotte bound).
