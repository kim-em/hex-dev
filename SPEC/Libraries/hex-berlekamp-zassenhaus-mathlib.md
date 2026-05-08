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

This library is thin — the hard work is split between
hex-berlekamp-zassenhaus (algorithmic correctness, Mathlib-free) and
hex-poly-z-mathlib (the Mignotte bound).
