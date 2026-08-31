# hex-poly-fp-mathlib (depends on hex-poly-fp + hex-poly-mathlib + hex-mod-arith-mathlib + Mathlib)

## Correspondence-only classification

This library is a `correspondence-only-layer`.

Computational conformance owners: `HexPoly`, `HexPolyFp`
Computational performance owners: `HexPoly`, `HexPolyFp`

The crossing point between the executable prime-field polynomial tower and
Mathlib's own polynomial type.

**Contents:**

- `fpPolyToPolynomial : FpPoly p → Polynomial (ZMod p)` and
  `polynomialToFpPoly` the other way.
- `fpPolyEquiv : FpPoly p ≃+* Polynomial (ZMod p)`, the ring equivalence they
  assemble into.
- `toMathlibPolynomial`, the forward map named for use in statements, with its
  coefficient, monicity, natural-degree, leading-coefficient, and `simp`
  lemmas; `coeff_polynomialToFpPoly` supplies the inverse coefficient rule.
- Transport lemmas naming the forward map for the operations a caller reaches
  for directly rather than through a `RingEquiv` composition: `derivative`,
  `mul`, `add`, `sub`, `neg`, `C`, general monomials, `X`, coefficient-sum
  evaluation, and composition. The inverse family covers zero, one, constants,
  negation, subtraction, addition, multiplication, and monomials.
- `toMathlibPolynomial_dvd_iff`, which both preserves executable divisibility
  and reflects a Mathlib divisibility witness back to the executable
  representation.
- `commRing : CommRing (FpPoly p)`, built from the ring laws hex-poly-fp proves
  rather than transported along `fpPolyEquiv`, so that the Mathlib operations
  are the executable ones and `sub` and `neg` are the executable ones too.
  Without it `FpPoly p →+* R` is not a well-formed type, so this is a
  prerequisite for every downstream ring homomorphism out of the executable
  polynomials rather than a convenience.
- `linearPow_eq_pow`, identifying hex-poly-fp's structural `linearPow` with the
  monoid power that `commRing` supplies, so `map_pow` applies to executable
  powers.
- `primeModulus_of_fact`, deriving the executable `ZMod64.PrimeModulus p`
  witness from Mathlib's `Fact (Nat.Prime p)`, and `hexPrime_of_fact`,
  deriving the executable `Hex.Nat.Prime p` from the same fact.
- The headline correctness theorem `squareFreeDecomposition_correct`
  (see below) with its transport chain: `pow_eq_pow` and
  `weightedProduct_eq_prod` identifying the executable square-and-multiply
  power and the weighted factor product with their Mathlib counterparts,
  `toMathlibPolynomial_{one, pow, weightedProduct}`, and the gcd-unit
  conversions `isCoprime_toMathlibPolynomial_of_normalizeMonic_gcd_eq_one`
  and `squarefree_toMathlibPolynomial_of_normalizeMonic_gcd_eq_one`.

Everything below this library is Hex's own tower: `DensePoly` over `ZMod64`,
reached through hex-poly-mathlib and hex-mod-arith-mathlib. Everything a
Mathlib user starts from is on the far side of `fpPolyEquiv`.

## Headline correctness theorem

`HexPolyFpMathlib.squareFreeDecomposition_correct`: the executable Yun
square-free decomposition is a genuine square-free decomposition in
`Polynomial (ZMod p)`. For a prime modulus and any input `f`, writing `d` for
`squareFreeDecomposition hp f` and `T` for `toMathlibPolynomial`:

- **reconstruction** — `C (toZMod d.unit)` times the product of
  `T sf.factor ^ sf.multiplicity` over `d.factors` equals `T f`;
- **square-freeness** — every transported factor `T sf.factor` is
  `Squarefree`;
- **pairwise coprimality** — the transported factors are pairwise
  `IsCoprime`;
- **positive multiplicities** — every recorded multiplicity is positive.

It needs no nonzeroness or degree hypothesis on `f`: the executable
post-conditions cover the degenerate cases (for `f = 0` the emitted unit is
`0`) and transport unchanged. It is built from the four Mathlib-free
post-conditions of `HexPolyFp.SquareFree`
(`squareFreeDecomposition_{weightedProduct, factors_squareFree,
pairwise_coprime, multiplicity_pos}`), with the gcd-unit certificates those
theorems emit — the monic normalization of the executable gcd reducing to
`1` — converted through the executable Bezout identity to `IsCoprime`, and
coprimality with the formal derivative reaching `Squarefree` via
`Polynomial.Separable`. A `#print axioms` guard pins its proof cone to the
three standard axioms.

## Ownership

Any library relating an `FpPoly`-backed construction to Mathlib depends on this
one: hex-gf2-mathlib composes the equivalence with the packed correspondence to
state `GF2Poly ≃+* Polynomial (ZMod 2)`, and the finite-field construction
libraries need it to speak about their moduli in Mathlib's terms. None of them
should have to depend on a factoring library to reach Mathlib.

hex-berlekamp-mathlib re-exports the names, so call sites spelling them
`HexBerlekampMathlib.fpPolyEquiv` resolve unchanged.

The equivalence needs only `ZMod64.Bounds p`, not primality: `FpPoly p` is a
ring for any admissible modulus, and so is `Polynomial (ZMod p)`. Primality
enters only through `primeModulus_of_fact`, which carries it as an explicit
`Fact (Nat.Prime p)` hypothesis. The coprimality transports that consume the
resulting witness are owned by the consumers, hex-berlekamp-mathlib in
particular, because they name that library's predicates.

The dependency on hex-poly-mathlib is narrow and worth naming, since it is not
the obvious one: the generic `DensePoly R ≃+* Polynomial R` cannot be reused
here, because `ZMod64` deliberately carries no Mathlib `Semiring` instance. The
edge exists for the list helper `list_getD_map_range_zero`, which the inverse
map's coefficient reasoning uses.

## What belongs here, and what does not

This library states the correspondence, the lemmas that follow from it alone,
and one designated exception: the headline correctness theorem
`squareFreeDecomposition_correct` for hex-poly-fp's own algorithmic surface,
together with the transport lemmas that compose into it. hex-poly-fp has no
other Mathlib companion, so the headline the per-library rule in
`PLAN/Conventions.md` requires lives here. Beyond that single theorem and its
supporting chain, algorithm-level lemmas stay out: a lemma that mentions
Berlekamp's `basisSize`, `isUnitPolynomial`, or Rabin's test belongs in
hex-berlekamp-mathlib even when its conclusion is about `toMathlibPolynomial`,
because it is a fact about the factoring algorithm rather than about the
representation.

## External comparators

No external comparator is required.

**Justification:** `correspondence-only-layer` per
`SPEC/benchmarking.md §"Comparator naming"`. The library introduces no
arithmetic algorithm; it transports values between two representations, and the
far side is Mathlib's own `Polynomial`. Two computational performance owners
carry the evidence, split by which library owns the operation being
transported. `FpPoly p` is `DensePoly (ZMod64 p)`, so the split is not the one
the library name suggests.

**hex-poly** owns the dense ring surface. `+`, `-`, `neg`, `*`, `derivative`,
`C` and `monomial` on `FpPoly p` are hex-poly's `DensePoly` operations at the
`ZMod64 p` coefficient ring, and the transport lemmas name them as such:
`toMathlibPolynomial_{add, sub, neg, mul, derivative, C, monomial}` are stated
about `Hex.DensePoly.*`, and `toMathlibPolynomial_X` about `Hex.FpPoly.X`,
which is `DensePoly.monomial 1 1`. `toMathlibPolynomial_dvd_iff` belongs here
too: both directions transport a multiplication witness and use the ring
equivalence, not division or gcd. So does `commRing`, whose `sub` and `neg`
fields are pinned to the executable `DensePoly` operations. The relevant
multiplication is the generic schoolbook convolution; hex-poly-fp's packed
`mulPacked` is an optional value-equal kernel, not the registered
implementation of `*`. Unreduced Horner composition is likewise hex-poly's
`DensePoly.compose`; this layer only proves its representation correspondence.
The `eval₂` coefficient-sum formula is proof-side normalization and introduces
no executable kernel to benchmark.

**hex-poly-fp** owns the prime-field surface above it: `linearPow`, and the
Frobenius, modular-composition, quotient-ring, square-free and monic-gcd
operations, together with the field-dependent gcd and modular division that
`primeModulus_of_fact` unlocks. Of these the layer transports `linearPow`, via
`linearPow_eq_pow`. `linearPow` has no bench target of its own, and correctly
so: it is a structural recursion defined for kernel reduction, its call
sites are theorems and private proof-side helpers, and the compiled
square-free path uses `pow` instead. The
value it denotes is `n` right-multiplications by the base, so its cost is
hex-poly's multiplication ladder iterated a declared number of times.
