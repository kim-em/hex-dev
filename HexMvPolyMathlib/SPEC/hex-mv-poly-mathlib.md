# hex-mv-poly-mathlib (depends on hex-mv-poly + hex-poly-mathlib + Mathlib)

The Mathlib bridge for the canonical, Mathlib-free sparse multivariate
polynomials in `hex-mv-poly`. It identifies
`Hex.MvPoly n R cmp` with `MvPolynomial (Fin n) R` while preserving the
executable operations and canonical representation supplied by the core
library.

## Scope

The bridge owns proof-facing structures and correspondence:

- `monoEquiv`, between fixed-length exponent vectors and Mathlib monomials;
- `toMvPolynomial` and `ofMvPolynomial`, with coefficientwise inverse laws;
- the ring equivalence `equiv` and algebra equivalence `algEquiv`;
- transported `CommSemiring`, `CommRing`, and `Algebra` instances whose
  operations are the executable `Hex.MvPoly` operations;
- the algebra homomorphism `aeval` and its constructor and arithmetic laws;
- correspondence for support, degree, evaluation, differentiation,
  homogeneous components, substitution, partial evaluation, renaming, and
  reordering; and
- recursive-view equivalences, including the zero-variable and one-variable
  dense-polynomial cases.

The sparse representation, monomial orders, algorithms, and their
Mathlib-independent proofs remain in `hex-mv-poly`.

## Principal equivalence

For a lawful monomial comparator:

```lean
def equiv [CommSemiring R] [DecidableEq R] :
    Hex.MvPoly n R cmp ≃+* MvPolynomial (Fin n) R
```

The equivalence is coefficientwise:

```lean
theorem coeff_toMvPolynomial [CommSemiring R] [DecidableEq R]
    (m : Hex.Mono n) (p : Hex.MvPoly n R cmp) :
    MvPolynomial.coeff (monoEquiv m) (toMvPolynomial p) =
      Hex.MvPoly.coeff m p
```

Its inverse builds the canonical sparse form, so the two round trips are
propositional equalities rather than quotient-level equivalences.

## Evaluation

`aeval` uses the executable core evaluator and agrees with Mathlib:

```lean
theorem aeval_apply [CommSemiring R] [DecidableEq R]
    [CommSemiring S] [Algebra R S]
    (x : Fin n → S) (p : Hex.MvPoly n R cmp) :
    aeval x p = MvPolynomial.aeval x (toMvPolynomial p)
```

The public API includes homomorphism laws for constants, variables, addition,
multiplication, powers, negation, and subtraction. This is the statement layer
needed by consumers such as `sos`; computation and certificate equality still
reduce through the Mathlib-free core.

## Verification

Every conversion theorem is proved from coefficient extensionality. The
bridge conformance target checks representative round trips and operation
correspondence against Mathlib's `MvPolynomial`. The monorepo also maintains
kernel-reduction proof probes for the downstream certificate patterns; those
are development benchmarks rather than part of the released package.

## External comparators

No external comparator is required. This is a Mathlib bridge: its relevant
comparison is the proved within-Lean correspondence with
`MvPolynomial (Fin n) R`; external systems would instead measure the
underlying sparse arithmetic owned by `hex-mv-poly`.
