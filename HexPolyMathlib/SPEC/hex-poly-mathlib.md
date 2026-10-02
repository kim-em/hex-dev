# hex-poly-mathlib (depends on hex-poly + Mathlib)

Proves the ring equivalence between `DensePoly R` and Mathlib's
`Polynomial R`:

```lean
def equiv [CommRing R] [DecidableEq R] : DensePoly R ≃+* Polynomial R
```

Also proves GCD/ExtGCD correspondence with Mathlib's `Polynomial.gcd`.

## Noninjective representation interpretation

For an executable representation `E` with ordinary operations and structural
`DecidableEq`, fix a lawful semantic field `K` and `eval : E → K`. Require
preservation of zero, one, natural casts and each operation used, together
with `eval e = 0 ↔ e = 0`. No injectivity or ring/field laws on `E` are assumed.
Keep the canonical core/Mathlib dictionaries on `K` fixed as in the existing
correspondence. The required map `interpret : DensePoly E → Polynomial K`
sends coefficient `i` to `eval (p.coeff i)`.

Prove preservation of zero and degree, arithmetic, derivative, Horner
application, and division/remainder for the actual executable algorithms.
The division statement identifies both interpreted outputs with Mathlib's
quotient and remainder, including zero divisors. Gcd corresponds after
normalization by a nonzero leading scalar; interpret the actual xgcd output
and its Bézout identity, rescaling witnesses together when making it monic.
For pseudo-division/gcd preserve the recorded scales and fraction-field
meaning, not an unscaled identity over an arbitrary domain.

Compose operation-only transfer lemmas from hex-poly with the existing
lawful-target correspondence. Selected-root evaluation and its zero-reflection
proof belong to hex-real-closure-mathlib, which instantiates this interface;
this library must not import the real-closure family. Distinct nonzero
representatives may have equal interpretation, so structural equality cannot
be used as a semantic equality decision. Scalar/polynomial semantic identities
use zero differences; literal context bindings retain exact equality.

## External comparators

No external comparator is required.

**Justification:** HexPolyMathlib is the correspondence library from
`Hex.DensePoly` to `Mathlib.Polynomial`; the relevant
comparison surface is the within-Lean `compare` group registering
Hex conversion targets against Mathlib's native polynomial-arithmetic
targets, per
`SPEC/benchmarking.md §"Within-Lean comparisons"`. Those
within-Lean compare groups exercise the same operations on
matched inputs and verify hash agreement; that is the relevant
shape of comparison for a correspondence library. External tools (FLINT
etc.) would compare against the underlying polynomial arithmetic,
which is HexPoly's surface and is covered there.


## Polynomial literal adapter request

[The `min_poly` frontend](../../HexMinPolyMathlib/SPEC/hex-min-poly-mathlib.md#the-min_poly-tactic)
requires a closed Mathlib polynomial literal adapter: recognize a polynomial
in the supported field codec, expose ascending coefficients, and prove the
identification with their decoded polynomial. Reuse this layer's polynomial
equivalence and the field codecs requested against
[hex-matrix-mathlib](../../HexMatrixMathlib/SPEC/hex-matrix-mathlib.md#requests-from-structural-tactic-frontends).
The initial carrier is `ℚ`; prime residues are a later codec extension.
`HexPolyMathlib.Literal.recognize` implements this adapter in `Literal.lean`,
returning ascending rational coefficients and an identification with
`polynomialOfList`. `LiteralData.lean` supplies the compiled rational coefficient operations and
public correspondence lemmas identifying them with Mathlib polynomial operations.
The frontend uses the integer-block proof path below.
`ScaledLiteral.lean` proves that shared integer coefficient blocks agree with
Mathlib polynomial operations. The identification proof uses those blocks and
integer cross products; coefficient addition, multiplication and powers do not
reduce rational normalization in the kernel. Scalar literals still use the
shared rational codec. The fragment includes
`C`, `X`, numerals, addition, subtraction, multiplication, negation and closed
natural powers. Unfolding is bounded at 64, exponents at 256 and coefficient
lists at 1024. Rational entries reuse `HexMatrixMathlib.Literal.evalEntry`;
the published dependency includes hex-matrix-mathlib. The consuming tactic
includes the adapter's proof in its one auxiliary theorem, and its complete
fresh-module probes include the adapter's elaboration cost.
