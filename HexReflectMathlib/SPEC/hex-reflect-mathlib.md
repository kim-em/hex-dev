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

The companion depends on `hex-reflect`, `hex-mv-poly-mathlib`,
`hex-mod-arith-mathlib`, and Mathlib.
It obtains `hex-mv-poly` and `hex-basic` transitively. No matrix,
row-reduction, determinant, characteristic-polynomial, gcd, or factorization
library is an implementation dependency. The modular arithmetic dependency
also brings its precompiled native library and GMP linkage into consumers of
this companion.

## Module layout

The Lake library is `HexReflectMathlib`, its namespace is
`HexReflectMathlib`, and `HexReflectMathlib.lean` is its umbrella. The
modules are `Carrier.lean` for carrier laws, `Residue.lean` for the residue
provider, and `Correspondence.lean` for polynomial theorems. It has no
independent conformance, benchmark, or proof-probe target;
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

## Positive-characteristic coefficients

`residueCoeffProvider p` supplies `Hex.ZMod64 p` coefficients when the
classified carrier reports positive characteristic `p`, `p` is prime,
`p < 2^31`, and the target has compatible Mathlib `Field F` and `CharP F p`
evidence. The registration has priority 5, above the universal integer
provider. Unknown characteristic and characteristic zero retain integer
coefficients. Mathlib's `Algebra.CharP.Basic`, imported transitively here,
provides a global bridge from `CharP` to Grind characteristic evidence for
cancellative semirings. Recognition is therefore automatic when instance
search finds that evidence. `isCharP_of_charP` remains a theorem for callers
that need to supply an exact instance explicitly. A concrete `ZMod p` field
requires Mathlib's usual `Fact (Nat.Prime p)` instance; the provider does not
install target field instances. When the modulus passes the prime and word
checks but no target `Field` instance is available, the provider is not
applicable and the universal integer provider remains available. This
includes prime-characteristic rings with zero divisors and concrete `ZMod p`
carriers lacking a `Fact (Nat.Prime p)` instance.

A recognized positive characteristic that is composite (or one) declines
with a prime-characteristic diagnostic. Moduli `p ≥ 2^31` decline with the
word-bound diagnostic before primality testing. For a recognized field,
missing Mathlib characteristic evidence and incompatible interpretation
operations decline with their reason. These declines stop fallback to the
integer provider.

The executable carrier uses `Hex.ZMod64.Bounds p` and
`Hex.ZMod64.PrimeModulus p`; the latter supports downstream `LawfulGcdOps`
without adding a gcd-library dependency here. The provider's `auxInstances`
contains quoted bounds, primality, and the scoped Mathlib ring instance for
consumers to introduce locally. Every auxiliary instance is type-checked by
provider validation. Consumers still synthesize or check their required
capability at the actual coefficient type: generic auxiliary evidence does
not itself certify a particular downstream capability. Its interpretation is
`residueHom p F`, the composite of `HexModArithMathlib.ZMod64.equiv` with
`ZMod.castHom`. `residueHom_injective` proves injectivity into every ring
of the same characteristic, in particular arbitrary field extensions of
`ZMod p`. `residueCoeffLaws` follows from `coeffLaws_ofRingHom`.
`CoeffLaws.changeRing` transfers those laws to the classified exact Grind
ring after checking definitional equality of its integer cast, zero, and
addition with the Mathlib operations. Other structure fields need not be
definitionally identical. The quoted coefficient operations are the named
executable `ZMod64` instances, independent of the caller's instance scope.
`residuePrime` deduces primality evidence from the field's nonzero
characteristic after this compatibility check succeeds. The runtime
recognizer uses the existing bounded trial-division test, but the kernel
does not replay that search to validate the auxiliary prime certificate. In particular, canonicalization can unfold
`ZMod p` to `Fin p`; the provider also tries the Mathlib `ZMod p` field
when its type is definitionally equal to the classified carrier. It never
accepts evidence from the type name alone.

The Mathlib `CommRing (Hex.ZMod64 p)` instance lives in
`HexModArithMathlib.Ring`, in scope `HexModArithMathlib.ZMod64`, which the
provider opens. It transports laws along the existing equivalence while
retaining executable zero, one, addition, subtraction, negation,
multiplication, powers, casts, and scalar multiplication. Division and
decidable equality are unchanged. The instance is scoped because the Mathlib
Grind reduct has different numeral instance expressions from the executable
ring. The
[determinant transport audit](../../HexDetMathlib/SPEC/hex-det-mathlib.md#outstanding-arm-and-carrier-obligations)
requires compatibility with executable operations; a scoped instance keeps
the existing explicit structure-selection discipline of those transports. Consumers open this scope when using the
Mathlib coefficient homomorphism.

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

`conformance/HexReflect/ResidueConformance.lean` checks the matrix
`!![x ^ 3 - x]` over `ZMod 3`: the quoted residue polynomial is `X₀³ − X₀`,
and its interpretation equals the matrix entry by a kernel-checked proof.
The residue provider also works with the coefficient-ring scope closed.
It also checks an abstract characteristic-three field, downstream instance
synthesis from the provider's auxiliary evidence at modulus five, and the
decline and integer-fallback paths. Existing reflection conformance remains
unchanged.

- Every carrier registration includes the exact instance expressions in its
  lookup identity.
- Open- and closed-`HexMvPolyMathlib`-scope instances cannot share a cache
  entry; both are accepted only when separately supported.
- The `MvPolynomial` theorem follows from the existing equivalence and the
  Mathlib-free soundness theorem.
- No source parser, computational algebra algorithm, or `native_decide` use is
  added.
- The import graph contains only `hex-reflect`, `hex-mv-poly-mathlib`,
  `hex-mod-arith-mathlib`, their transitive dependencies, and Mathlib.
