/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexHensel.Multifactor
import HexHensel.QuadraticMultifactor
import HexHenselMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexHensel: executable Hensel lifting" =>
%%%
tag := "hex-hensel"
%%%

# Introduction
%%%
tag := "hex-hensel-intro"
%%%

`HexHensel` does executable Hensel lifting. Hensel lifting turns a
factorization known only modulo a prime `p` into a factorization modulo
a prime power `p^k`: given `f ≡ g · h (mod p)` together with a Bezout
certificate `s · g + t · h ≡ 1 (mod p)`, it refines `g` and `h` step by
step until they multiply to `f` modulo `p^k`. The precision `k` is
chosen large enough (via a Mignotte bound) that the lifted factors
coincide with the true integer factors. This connects the prime-field
factorization in `HexPolyFp` to the integer factorization pipelines
built on top of it.

The library connects integer polynomials
({ref "hex-poly-z"}[HexPolyZ], `Hex.ZPoly`) with prime-field
polynomials (`HexPolyFp`, `Hex.FpPoly p`). It provides coefficientwise
reduction modulo powers of `p`, the linear and quadratic single-step
corrections, the iterative {name}`Hex.ZPoly.henselLift` wrapper, and the
ordered multifactor lift API the factorization pipeline consumes. It is
Mathlib-free and depends only on `HexPolyFp` and `HexPolyZ`. See
{ref "hex-hensel-cross-references"}[Cross-references].

# Coefficientwise reduction
%%%
tag := "hex-hensel-reduction"
%%%

Every lift step works modulo a fixed modulus, so the primitive
operation is reduction of each integer coefficient to its canonical
representative in `[0, modulus)`. {name}`Hex.ZPoly.reduceModPow` reduces
modulo a prime power `p^k`, and {name}`Hex.QuadraticLiftResult.reduceModSquare`
is the squaring-step specialization that reduces modulo `m^2`.

{docstring Hex.ZPoly.reduceModPow}

{docstring Hex.QuadraticLiftResult.reduceModSquare}

The reduced polynomial is congruent to the original modulo the modulus.
Every later step relies on this to preserve the factorization relation
across reductions.

{docstring Hex.ZPoly.congr_reduceModPow}

## Worked example: coefficient reduction
%%%
tag := "hex-hensel-worked-reduction"
%%%

The block below reduces the coefficients of `100 - 3x + 50x²`. Modulo
`7² = 49` the coefficients become `2, 46, 1`; modulo `5² = 25` they
become `0, 22, 0`, and the trailing zero is trimmed by normalization.

```lean
open Hex Hex.DensePoly Hex.QuadraticLiftResult

namespace HexHenselChapterReduce

private def f : ZPoly := ofCoeffs #[100, -3, 50]

-- 100 ≡ 2, -3 ≡ 46, 50 ≡ 1  (mod 7² = 49)
private def a : ZPoly := ZPoly.reduceModPow f 7 2
#guard a.toArray.toList = [2, 46, 1]

-- 100 ≡ 0, -3 ≡ 22, 50 ≡ 0  (mod 5² = 25)
private def b : ZPoly := reduceModSquare f 5
#guard b.toArray.toList = [0, 22]

end HexHenselChapterReduce
```

# Single-step corrections
%%%
tag := "hex-hensel-steps"
%%%

Hensel lifting comes in two flavours that differ in how fast the
precision grows. The *linear* step refines the modulus by one prime
power per step (`p^k → p^(k+1)`); the *quadratic* step doubles it
(`m → m^2`), reaching precision `p^k` in `O(log k)` steps rather than
`O(k)`, at the cost of also lifting the Bezout witnesses each step.

The linear step returns the corrected pair of factors.

{docstring Hex.LinearLiftResult}

{docstring Hex.ZPoly.linearHenselStep}

The quadratic step doubles the modulus and so must carry the Bezout
witnesses forward alongside the factors. Its result bundles all four.

{name}`Hex.QuadraticLiftResult` packages the updated leading factor `g`
(monic), the complementary factor `h`, and the updated Bezout witnesses
`s` and `t` satisfying `s · g + t · h ≡ 1 (mod m²)`.

{docstring Hex.ZPoly.quadraticHenselStep}

# Iterative and multifactor lifts
%%%
tag := "hex-hensel-multifactor"
%%%

{name}`Hex.ZPoly.henselLift` iterates the linear step to lift a single
two-factor split all the way from modulus `p` to `p^k`.

{docstring Hex.ZPoly.henselLift}

Factorization pipelines need to lift an *ordered list* of mod-`p`
factors simultaneously, not just a single split. The multifactor API
does this by a sequential binary split tree: at each node it lifts the
first factor against the product of the rest, then recurses. There are
linear and quadratic-doubling versions. The factorization pipeline uses
the quadratic one, because of its `O(log k)` precision growth.

{docstring Hex.ZPoly.multifactorLift}

{docstring Hex.ZPoly.multifactorLiftQuadratic}

# Key correctness theorems
%%%
tag := "hex-hensel-correctness"
%%%

The defining guarantee of each lifter is that the product of the lifted
factors is congruent to the input modulo the target prime power. For the
iterative single-split wrapper:

{docstring Hex.ZPoly.henselLift_spec}

The multifactor lifters carry the same product-congruence guarantee. The
proof maintains it at each node of the recursive split.

{docstring Hex.ZPoly.multifactorLift_spec}

{docstring Hex.ZPoly.multifactorLiftQuadratic_spec}

The quadratic doubling loop is verified against an explicit loop
invariant: the three facts a caller must maintain across one doubling
(product congruence, Bezout congruence, and monicity of the leading
factor) are exactly the preconditions the doubling step requires.

{docstring Hex.ZPoly.QuadraticLiftLoopInvariant}

{docstring Hex.ZPoly.quadraticLiftLoopInvariant_step}

Monicity of the leading factor is preserved by the whole quadratic
multifactor lift, so a monic input yields monic lifted factors, which
the factorization pipeline requires.

{docstring Hex.ZPoly.multifactorLiftQuadratic_each_monic}

# The Mathlib correspondence
%%%
tag := "hex-hensel-mathlib"
%%%

Everything above is executable and Mathlib-free. `HexHenselMathlib`
proves it correct against Mathlib's `Polynomial`: the factorization the
executable routine lifts is genuine modulo `p ^ k`, it extends the input
factorization mod `p`, it preserves degrees, and it is unique among
coprime monic lifts with the same reduction mod `p`.

{docstring HexHenselMathlib.hensel_correct}

{docstring HexHenselMathlib.hensel_extends}

{docstring HexHenselMathlib.hensel_degree}

{docstring HexHenselMathlib.hensel_unique}

# Cross-references
%%%
tag := "hex-hensel-cross-references"
%%%

`HexHensel` depends on the polynomial representation libraries, and the
integer-factorization libraries depend on it:

* {ref "hex-poly-z"}[HexPolyZ] supplies the integer polynomial type
  `Hex.ZPoly`, the coefficientwise congruence predicate the lift
  invariants are stated against, and the executable Mignotte bound that
  fixes the target precision `k`. `HexPolyFp` supplies the prime-field
  type `Hex.FpPoly p` and the mod-`p` Bezout witnesses that seed a lift.
* Downstream, the integer Berlekamp–Zassenhaus factorization pipeline
  consumes {name}`Hex.ZPoly.multifactorLiftQuadratic` to lift its
  mod-`p` factorizations to working precision.
