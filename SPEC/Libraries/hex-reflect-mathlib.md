# hex-reflect-mathlib (Mathlib translations for hex-reflect)

`hex-reflect-mathlib` is the Mathlib companion to
[hex-reflect](hex-reflect.md). It translates supported Mathlib carriers into
the provider and coefficient-interpretation records defined by
`Hex.Reflect`, and states the `MvPolynomial` form of the conversion theorem.
It contains no symbolic algorithm.

This is a specification. It does not add an implementation.

## Dependencies

The companion depends on `hex-reflect`, `hex-mv-poly-mathlib`, and Mathlib.
It obtains `hex-mv-poly` and `hex-basic` transitively. No matrix,
row-reduction, determinant, characteristic-polynomial, gcd, or factorization
library is an implementation dependency.

## Carrier translations

A carrier translation records the exact Mathlib carrier and exact algebraic
instances, its executable coefficient representation when one is needed, the
interpretation map, and proofs that the operations used by reflection commute
with interpretation. Registrations are keyed by those expressions, not by a
type name.

The initial file set contains only translations needed by the first Mathlib
frontends. Adding a carrier does not add syntax to `Lean.Meta.Sym.Arith` and
does not alter atom allocation. Unsupported operations in a supported carrier
remain atoms.

## `MvPolynomial` correspondence

`HexMvPolyMathlib.equiv` already has type

```lean
Hex.MvPoly n R cmp ≃+* MvPolynomial (Fin n) R
```

and `HexMvPolyMathlib.algEquiv` supplies the corresponding algebra
equivalence. This companion reuses those declarations. It does not define a
second conversion between the polynomial types.

For a sealed reflection environment, the companion proves that applying
`HexMvPolyMathlib.equiv` to the converted `Hex.MvPoly` gives the
`MvPolynomial` whose coefficients and `Fin n` variables are the translated
reflected coefficients and atoms. Evaluating that `MvPolynomial` with
`MvPolynomial.aeval` gives the same source value as the
`Hex.Reflect` interpretation theorem.

The proof is a composition of:

1. the Mathlib-free conversion soundness theorem from `hex-reflect`;
2. `HexMvPolyMathlib.equiv_apply` or `algEquiv_apply`;
3. the existing evaluation correspondence, including
   `HexMvPolyMathlib.evalHorner_eq_aeval` where the Horner form is used.

It does not reify the source expression again and does not use Mathlib's
`ring` tactic to certify each converted input.

## Non-goals

This library does not implement determinant, rank, characteristic polynomial,
normalization, gcd, factorization, or provider search. It does not own matrix
literal parsing or tactic syntax. Those operations live in their respective
consumer libraries and depend on this companion only when their source and
result statements use Mathlib types.

It also does not move `HexMvPolyMathlib.equiv`, duplicate its proofs, or make
the Mathlib-free `hex-reflect` library depend on Mathlib.

## Verification requirements

- Every carrier registration includes the exact instance expressions in its
  lookup identity.
- The `MvPolynomial` theorem follows from the existing equivalence and the
  Mathlib-free soundness theorem.
- No source parser, computational algebra algorithm, or `native_decide` use is
  added.
- The import graph contains only `hex-reflect`, `hex-mv-poly-mathlib`, their
  transitive dependencies, and Mathlib.
