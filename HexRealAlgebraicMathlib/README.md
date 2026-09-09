# hex-real-algebraic-mathlib

The Mathlib companion to [hex-real-algebraic](../HexRealAlgebraic/README.md),
developed in the Hex monorepo and not yet published separately.

```lean
import HexRealAlgebraicMathlib

open Hex

example (a : RealAlgebraicNumber) : IsAlgebraic ℚ a.toReal :=
  RealAlgebraicNumber.isAlgebraic a

example (a : RealAlgebraicNumber) :
    (a ^ 2).sqrt (sq_nonneg a) = a.abs :=
  RealAlgebraicNumber.sqrt_square a

example : IsRealClosed RealAlgebraicNumber := inferInstance
```

The companion supplies `Field`, `LinearOrder`, `IsStrictOrderedRing`,
`FloorRing`, and `IsRealClosed`. Its field and order dictionaries retain the
computational operations; [Instances.lean](Instances.lean) checks their
coherence by definitional equality. It also proves the `Laws` witness needed
by the Mathlib-free core order and `grind` dictionaries.

`RealAlgebraicNumber.toReal` is injective, with ring homomorphism `toRealHom`
and order embedding `toRealOrderEmbedding`. `range_toReal` characterizes its
image as precisely the real numbers algebraic over ℚ. Correspondence theorems
cover arithmetic, casts, comparison, extrema, sign, absolute value, square
roots, rounding, rational recognition, approximation, and representation
round trips.

`RealAlgebraicPoly.toPolynomial` interprets real coefficient arrays in `ℝ[X]`;
`ofPolynomial` converts a Mathlib polynomial into the executable representation.
The root theorems prove completeness, multiplicity agreement, and strict
ordering. Real-closedness uses the executable root driver to recover witnesses
for square closure and odd-degree root existence, without assuming an
`IsRealClosed ℝ` instance.

Build with `lake build HexRealAlgebraicMathlib`. This is a correspondence-only
layer; executable fixtures and external oracle checks belong to the
computational library. See the
[joint specification](../SPEC/Libraries/hex-real-algebraic.md) for the dependency
contract and theorems required of replacement comparison implementations.
