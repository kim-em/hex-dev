# hex-berlekamp-zassenhaus-mathlib (depends on hex-berlekamp-zassenhaus + hex-poly-z-mathlib)

Instantiates the conditional correctness theorems from
hex-berlekamp-zassenhaus (which take an abstract coefficient bound)
with the Mignotte bound from hex-poly-z-mathlib, giving unconditional
results. All statements use the `Factorization` record from
`hex-berlekamp-zassenhaus.md`'s output-convention section.

The headline theorems below hold over the **cost-based hybrid `factorize`**
(the `factorClassical` / `factorLattice` / `factorTrial` tiers). By the
tier-result-equivalence and dispatch-soundness contracts (main spec
§*Invariant contracts and dispatch soundness*), `factorize`'s output is
independent of which tier the dispatcher selects, so these theorems
reduce to the per-tier correctness — Group A for the classical tier,
Group B for the lattice tier, Group C for the combinator. Per the
project's performance-led principle (`SPEC/design-principles.md`), these
proofs adapt to the committed executable tiers; the implementation is
not reshaped to ease them.

```lean
theorem factorize_product (f : ZPoly) :
    Factorization.product (ZPoly.factorize f) = f

theorem factorize_irreducible_of_nonUnit (f : ZPoly) :
    ∀ (g, m) ∈ (ZPoly.factorize f).factors, Hex.ZPoly.Irreducible g

theorem factorize_unique (f : ZPoly) (φ ψ : Factorization) :
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

`factorize_irreducible_of_nonUnit` is the corrected form of the old
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

**Correctness of the executable checker.** The biconditional linking
the Mathlib-free `isIrreducible` *checker* to the `Irreducible`
*class* lives here, not in `hex-berlekamp-zassenhaus`, because it is
equivalent to the full forward correctness of `factorize` (Group C; see
that library's §`Mathlib-free Hex.ZPoly.Irreducible class` for why a
Mathlib-free file cannot state it):

```lean
theorem Hex.ZPoly.isIrreducible_iff (f : ZPoly) :
    Hex.ZPoly.isIrreducible f = true ↔ Hex.ZPoly.Irreducible f

instance (f : ZPoly) : Decidable (Hex.ZPoly.Irreducible f) :=
  decidable_of_iff _ (Hex.ZPoly.isIrreducible_iff f)
```

The forward direction follows from C1 (`factorize f` is the irreducible
factorisation): a single primitive unit-scalar factor of multiplicity
one is `f` itself up to a unit, and completeness of `factorize` rules out
any finer decomposition. The backward direction is the converse. The
constant case reduces to `Nat.Prime` decidability. This is the only
route to `decide`-ing `Hex.ZPoly.Irreducible` for concrete inputs;
Mathlib-free consumers (e.g. `HexNumberField`) must instead thread
`[Hex.ZPoly.Irreducible p]` as an instance argument.

Also connects to Mathlib's `Polynomial ℤ` and provides
`Decidable (Irreducible f)` for `f : Polynomial ℤ`.

This library is thin — the hard work is split between
hex-berlekamp-zassenhaus (algorithmic correctness, Mathlib-free) and
hex-poly-z-mathlib (the Mignotte bound).

## The `factor_poly` / `irreducibility` provider

This library declares the third `factor_poly`/`irreducibility` provider
(`HexBerlekampZassenhausMathlib.FactorTactic.provider`, probed by name from
`Hex.FactorTactic.providerNames` after the free `Hex.ZPoly` provider and
the `Polynomial (ZMod q)` bridge provider), with two arms:

- **`Polynomial ℤ`** (term forms, tactic forms, and goal mode): a
  parser-with-proof interprets the input over
  `X / C / numerals / + / - / * / neg / ^ (Nat literal)` (interpreter shared
  with `isolate_roots`: `HexPolyZMathlib.PolyParse`), simultaneously
  evaluating to an executable `Hex.ZPoly` and building
  `hP : toPolynomial f = P` through the named `toPolynomial_*` transport
  lemmas. The compiled factorizer runs as untrusted search; per-factor
  irreducibility is certified by a free-layer `Hex.ZPoly.IrredWitness` where
  one exists and by a multi-prime degree-obstruction certificate
  (`Hex.certifyIrreducible?`) otherwise; emitted terms apply the
  kernel-decidable assemblers `Hex.FactoredPoly.ofZ` / `irreducible_ofZ`
  (`FactorTransport.lean`) to reified literals with every Boolean slot
  discharged by `Eq.refl true`. The factorizer never appears in emitted
  terms.
- **Strong `Hex.ZPoly`**: probed after the free provider, so it only sees
  the balanced inputs the free layer declines. It certifies them through
  reified multi-prime certificates replayed by `checkIrreducibleCertLinear`,
  concluding in the free layer (`Hex.ZPoly.Irreducible f`, via
  `zpolyIrreducible_of_checkIrreducibleCertLinear`) and assembling mixed
  factor covers through the bulk checker `checkMultiPrimeCover`.

Goal-mode `irreducibility` closes `Hex.ZPoly.Irreducible f`,
`Irreducible (HexPolyZMathlib.toPolynomial f)`, and `Irreducible P` for
parseable `P : Polynomial ℤ`. The `toPolynomial` goal shape subsumes the
old `irreducible_cert` tactic, which is deleted.

Inputs whose modular factorizations are balanced at every candidate prime,
that are not Eisenstein at any small shift (the free layer certifies e.g.
`X⁴+1` that way), *and* whose proper factor degrees are not jointly
obstructed by the per-prime degree-sum language (e.g. Swinnerton-Dyer
polynomials) have no certificate in either language; the provider declines
with a diagnostic pointing at the kernel-decide fallbacks.

## The kernel-decide fallbacks `irreducibility!` / `factor_poly!`

`BangElab.lean` declares bang variants of both tactics (term, tactic, and
goal forms). Each first runs the normal certificate pipeline; on failure it
falls back to a kernel `decide` through
`Hex.ZPoly.instDecidableIrreducible` — the emitted proof is
`Hex.ZPoly.irreducible_of_decide f (Eq.refl true)` (or its `Polynomial ℤ` /
`Factored` transports `irreducible_ofZ_decide` /
`Hex.FactoredPoly.ofZDecide`), so the kernel re-runs the full
Berlekamp-Zassenhaus factorizer to verify it. This is the only route for
balanced inputs outside both certificate languages.

Two costs land on the *calling* module (see the `BangElab` module
docstring): it must `import all` the executable closure (the factorizer's
bodies are not `@[expose]`d, and non-exposed bodies are invisible to a
downstream module's kernel — this includes core modules such as
`Init.Data.Fin.Fold`; `FactorPolyTests.lean` carries a working block), and
the kernel replay costs real time (quartics sub-second, degree 8 seconds,
degree 12 tens of seconds; a dense-size budget of 13 rejects larger inputs
at elaboration time). The elaborator prechecks kernel reducibility with
`Lean.Kernel.whnf`, so a missing closure fails with a clear message rather
than a kernel type mismatch. Inputs routed to the lattice tier cannot be
certified this way (the FFI `lllNative` has no kernel-reducible body).
The plain (non-bang) forms never run the factorizer in the kernel.
