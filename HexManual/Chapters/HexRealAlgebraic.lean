/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import VersoManual
import HexRealAlgebraicMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "HexRealAlgebraic: exact real values and complex coordinates" =>
%%%
tag := "hex-real-algebraic"
%%%

`HexRealAlgebraic` is an incubating library in `hex-dev`; it is not yet a
published split package. It represents a real algebraic number as a canonical
algebraic number with an exact reality check. Import `HexRealAlgebraic` for
execution, or `HexRealAlgebraicMathlib` for the verified ordered field and
real-closedness results. The computational library has no Mathlib dependency.

# Construction and exact order

{name}`Hex.RealAlgebraicNumber.ofAlgebraic?` rejects nonreal values.
Arithmetic and casts preserve the subtype, using the existing canonical
arithmetic and an exact reality check. Equality stays structural. Unlike
the complex partial order, comparison of real algebraic values is total.
The computational instances support Lean core order classes and `grind`;
the companion supplies `LinearOrder` and the ordered-field laws.

```lean
open Hex

namespace HexRealAlgebraicChapter

def s : RealAlgebraicNumber :=
  (RealAlgebraicNumber.ofAlgebraic? (ZPoly.rootNear #p[-2, 0, 1] 1.4)).getD 0

#guard RealAlgebraicNumber.ofAlgebraic? AlgebraicNumber.I == none
#guard (1 : RealAlgebraicNumber) < s
#guard s < RealAlgebraicNumber.ofRat (14143 / 10000)
#guard compare s ((s + 1) - 1) == .eq
#guard max s (-s) == s
#guard min s (-s) == -s
#guard (-s).sign == -1
#guard (-s).abs == s
```

{name}`Hex.RealAlgebraicNumber.floor` and {name}`Hex.RealAlgebraicNumber.ceil`
return exact integers. {name}`Hex.RealAlgebraicNumber.toRat?` succeeds exactly
for rational values. {name}`Hex.RealAlgebraicNumber.approx` returns a dyadic
centre with absolute error at most `2^(-prec)`, including at negative precisions;
`approxBall` retains the enclosing ball. `Repr` prints a checked construction
that rebuilds the same value.

```lean
#guard s.floor == 1
#guard (-s).floor == -2
#guard s.ceil == 2
#guard s.toRat? == none
#guard (RealAlgebraicNumber.ofRat (-3 / 2)).toRat? == some (-3 / 2)
#guard (s.approx 8).toRat > 1
```

# Real roots

{name}`Hex.ZPoly.realAlgebraicRoots` returns distinct real roots of an integer
polynomial, sorted by exact value. {name}`Hex.RealAlgebraicPoly.roots` accepts
real algebraic coefficients and returns the real roots with multiplicities,
also sorted by exact value. Its zero polynomial returns `RealRootSet.all`;
`toArray` is empty in that case, so inspect the root set when zero is possible.

{name}`Hex.RealAlgebraicNumber.sqrt?` returns the nonnegative square root,
or `none` for a negative argument. The total `sqrt` takes a proof of
nonnegativity. It shares the complex radical selector, exactifying only the
winning lazy root when interval selection succeeds. This agrees with the complex principal square root on its
domain, as proved by {name}`Hex.AlgebraicNumber.sqrt_ofReal`.

```lean
#guard (RealAlgebraicNumber.sqrt? (s * s)) == some s
#guard (RealAlgebraicNumber.sqrt? (-1)) == none
#guard (ZPoly.realAlgebraicRoots #p[-2, 0, 1]).size == 2
example : LinearOrder RealAlgebraicNumber := inferInstance
example : IsRealClosed RealAlgebraicNumber := inferInstance
```

# Real and imaginary parts

Importing this library adds {name}`Hex.AlgebraicNumber.re` and
{name}`Hex.AlgebraicNumber.im`, both returning `RealAlgebraicNumber`.
{name}`Hex.AlgebraicNumber.ofReal` includes a real value into the complex
algebraic numbers, also available as a coercion. The real layer owns these
projections to keep the dependency graph acyclic: number fields do not depend
on their real subtype library.

The formulas are `(a + a.conj)/2` and `(a - a.conj)/(2I)`. Real inputs have
direct paths; general projections perform exact algebraic arithmetic and
may require factoring. The companion proves reconstruction, extensionality,
and the addition, multiplication, subtraction, and conjugation formulas.

```lean
def z : AlgebraicNumber := s.toAlgebraic + AlgebraicNumber.I
#guard z.re == s
#guard z.im == 1
#guard z.conj.re == z.re
#guard z.conj.im == -z.im

example (a : AlgebraicNumber) :
    a.re.toAlgebraic + a.im.toAlgebraic * AlgebraicNumber.I = a :=
  AlgebraicNumber.re_add_im a

example (a b : AlgebraicNumber) : a ≤ b ↔ a.re ≤ b.re ∧ a.im = b.im :=
  AlgebraicNumber.le_parts a b

end HexRealAlgebraicChapter
```

# Complex norms

{name}`Hex.AlgebraicNumber.normSq` and {name}`Hex.AlgebraicNumber.abs` return
`RealAlgebraicNumber`. The squared norm is `a * a.conj`; the modulus is its
nonnegative square root. For real inputs, modulus uses the existing real
absolute value directly. General inputs use exact arithmetic and root finding.
These functions belong to the real library so the computational dependencies
remain acyclic.

```lean
#guard (3 + 4 * AlgebraicNumber.I).normSq == 25
#guard (3 + 4 * AlgebraicNumber.I).abs == 5
example (a : AlgebraicNumber) : a.abs ^ 2 = a.normSq :=
  AlgebraicNumber.abs_sq a
example (a b : AlgebraicNumber) : (a * b).abs = a.abs * b.abs :=
  AlgebraicNumber.abs_mul a b
```

The companion identifies them with `Complex.normSq` and the complex norm,
and proves nonnegativity, zero characterization, conjugation invariance,
and multiplicativity.

See {ref "hex-number-field-complex-api"}[complex conjugation and radicals] for
branch conventions, and {ref "hex-number-field-common-field"}[common fields]
for converting several algebraic values to one rational power basis.
