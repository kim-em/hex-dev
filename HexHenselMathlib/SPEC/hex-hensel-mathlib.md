# hex-hensel-mathlib (depends on hex-hensel + hex-poly-mathlib + Mathlib)

Proves correctness of Hensel lifting algorithms and the uniqueness
theorem for coprime polynomial factorization lifting.

**Key lemma — coprimality lifts through p^k:**
```lean
theorem coprime_mod_p_lifts (g h : Polynomial ℤ) (p : ℕ) (k : ℕ)
    [Fact (Nat.Prime p)] (hk : 0 < k) :
    IsCoprime (g.map (Int.castRingHom (ZMod p)))
              (h.map (Int.castRingHom (ZMod p))) →
    IsCoprime (g.map (Int.castRingHom (ZMod (p ^ k))))
              (h.map (Int.castRingHom (ZMod (p ^ k))))
```
Proof: choose Bezout coefficients mod `p`, lift their coefficients to
`ZMod (p^k)` via the surjective reduction map `ZMod (p^k) → ZMod p`.
The lifted combination equals `1 + p·u`; since `p·u` is nilpotent in
`ZMod (p^k)` (`(p·u)^k = 0`), the element `1 + p·u` is a unit.
Multiply the lifted Bezout identity by its inverse.

**Correctness theorems** (transferred from hex-hensel via ring equiv
`DensePoly Int ≃+* Polynomial ℤ`):
```lean
theorem hensel_correct (f g h : ZPoly) (p k : Nat) (s t : FpPoly p) :
    let r := henselLift p k f g h s t
    (r.g.map φ) * (r.h.map φ) = f.map φ
  where φ := Int.castRingHom (ZMod (p ^ (k + 1)))

theorem hensel_extends (f g h : ZPoly) (p k : Nat) (s t : FpPoly p) :
    (henselLift p k f g h s t).g.map φ = g.map φ
  where φ := Int.castRingHom (ZMod (p ^ k))

theorem hensel_degree (f g h : ZPoly) (p k : Nat) (s t : FpPoly p) :
    (henselLift p k f g h s t).g.degree = g.degree
```

**Uniqueness theorem:**
```lean
theorem hensel_unique (f g h g' h' : Polynomial ℤ) (p : ℕ) (k : ℕ)
    [Fact (Nat.Prime p)] (hk : 0 < k)
    (hg : g.Monic) (hg' : g'.Monic)
    (hdeg : g.natDegree = g'.natDegree)
    (hprod : (g.map φₖ) * (h.map φₖ) = f.map φₖ)
    (hprod' : (g'.map φₖ) * (h'.map φₖ) = f.map φₖ)
    (hg1 : g.map φ₁ = g'.map φ₁)
    (hh1 : h.map φ₁ = h'.map φ₁)
    (hcop : IsCoprime (g.map φ₁) (h.map φ₁)) :
    g.map φₖ = g'.map φₖ ∧ h.map φₖ = h'.map φₖ
  where
    φₖ := Int.castRingHom (ZMod (p ^ k))
    φ₁ := Int.castRingHom (ZMod p)
```

**Proof of `hensel_unique`** (induction on `k`):
- Base `k = 1`: immediate from hypotheses `hg1`, `hh1`.
- Inductive step: by IH, `g' ≡ g + p^n · A` and `h' ≡ h + p^n · B`
  mod `p^(n+1)`. Product equality gives `A·h + B·g = 0` in
  `(ZMod p)[X]`. Since `gcd(g,h) = 1` mod `p`, we get `g | A·h`,
  hence `g | A`. Monicity of `g` and `g'` with `natDegree g =
  natDegree g'` gives `natDegree A < natDegree g`, so `A = 0`.
  Then `B·g = 0` in `(ZMod p)[X]`; since `g` is monic (nonzero) and
  `(ZMod p)[X]` is a domain, `B = 0`.

Note: `coprime_mod_p_lifts` is NOT needed for the induction step
(the divisibility argument uses coprimality mod `p`, not mod `p^n`).
It is needed separately by hex-berlekamp-zassenhaus-mathlib for
lifting Bezout coefficients.

**Mathlib infrastructure used:**
- `Polynomial.map` + `map_mul`, `map_sub` (congruences as equalities)
- `IsCoprime.map` (coprimality through ring homs)
- `EuclideanDomain` for `Polynomial (ZMod p)` (GCD, Bezout — ZMod p only)
- `C_dvd_iff_dvd_coeff` (coefficient-wise divisibility)
- `Monic.map`, `Monic.natDegree_mul` (degree control)
- `map_divByMonic`, `map_modByMonic` (division commutes with ring homs)

Do NOT use `EuclideanDomain` over `ZMod (p^k)` for `k > 1` — it is
not a field. Use monic division there.

**Glue lemmas to prove locally:**
- Coefficient divisibility ↔ equality after `Polynomial.map`
- Exactness of coefficient-wise `Int.div` (if `p^k ∣ coeff`, then
  mapping `coeff / p^k` gives the expected quotient mod `p`)
- Map compatibility for `ZMod (p^(k+1)) → ZMod (p^k) → ZMod p`
- Nilpotent/unit lemma for `1 + p·u` in `Polynomial (ZMod (p^k))`
