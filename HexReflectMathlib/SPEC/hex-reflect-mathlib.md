# hex-reflect-mathlib (Mathlib translations for hex-reflect)

`hex-reflect-mathlib` is the Mathlib companion to
[hex-reflect](../../HexReflect/SPEC/hex-reflect.md). It translates supported Mathlib carriers into
the provider and coefficient-interpretation records defined by
`Hex.Reflect`, and states the `MvPolynomial` form of the conversion theorem.
It contains no symbolic algorithm.

The implementation lives in `HexReflectMathlib`.

This is a correspondence-only-layer.

Computational conformance owner: `HexReflect`.

Computational performance owner: `HexReflect`.

## Dependencies

The companion depends on `hex-reflect`, `hex-mv-poly-mathlib`, and Mathlib.
It obtains `hex-mv-poly` and `hex-basic` transitively. No matrix,
row-reduction, determinant, characteristic-polynomial, gcd, or factorization
library is an implementation dependency.

## Module layout

The Lake library is `HexReflectMathlib`, its namespace is
`HexReflectMathlib`, and `HexReflectMathlib.lean` is its umbrella. The initial
modules are `Carrier.lean` for registrations and `Correspondence.lean` for
theorems. It has no independent conformance, benchmark, or proof-probe target;
the computational owner tests each registration and conversion path.

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

Importing this companion does not open the `HexMvPolyMathlib` scope globally.
A frontend re-synthesizes and canonicalizes its requested structures in its
actual scope. Open- and closed-scope Grind instances are distinct exact
instance identities; a registration may support both explicitly, but provider
lookup and caches never identify them solely from the carrier type.

## `MvPolynomial` correspondence

For a coefficient type `C`, `HexMvPolyMathlib.equiv` already has type

```lean
Hex.MvPoly n C cmp ≃+* MvPolynomial (Fin n) C
```

under `[CommSemiring C] [DecidableEq C]`, `Std.TransCmp cmp`, and
`Std.LawfulEqCmp cmp`; `HexMvPolyMathlib.algEquiv` supplies the corresponding
algebra equivalence. This companion reuses those declarations. It does not
define a second conversion between the polynomial types.

For a sealed reflection environment, the companion proves that applying
`HexMvPolyMathlib.equiv` to the converted `Hex.MvPoly` gives the
`MvPolynomial` whose coefficients and `Fin n` variables are the translated
reflected coefficients and atoms. If the source carrier is `R`, its provider
supplies a coefficient homomorphism `C →+* R`. Evaluation uses
`MvPolynomial.eval₂` (or `eval₂Hom`) with that homomorphism and the atom
valuation. The corresponding executable statement uses
`HexMvPolyMathlib.eval₂MathlibHom` and
`HexMvPolyMathlib.eval₂MathlibHom_apply`. `MvPolynomial.aeval` is used only in
the special case where an `Algebra C R` supplies the coefficient map.

The proof is a composition of:

1. the Mathlib-free conversion soundness theorem from `hex-reflect`;
2. `HexMvPolyMathlib.equiv_apply` or `algEquiv_apply`;
3. `HexMvPolyMathlib.eval₂MathlibHom_apply`, or the existing algebra-evaluation
   correspondence when an `Algebra C R` is part of the provider.

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
- Open- and closed-`HexMvPolyMathlib`-scope instances cannot share a cache
  entry; both are accepted only when separately supported.
- The `MvPolynomial` theorem follows from the existing equivalence and the
  Mathlib-free soundness theorem.
- No source parser, computational algebra algorithm, or `native_decide` use is
  added.
- The import graph contains only `hex-reflect`, `hex-mv-poly-mathlib`, their
  transitive dependencies, and Mathlib.
