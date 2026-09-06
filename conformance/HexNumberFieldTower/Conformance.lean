/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexNumberFieldTower

/-!
Core conformance checks for `HexNumberFieldTower`.

Oracle: PARI/GP through cypari2 for the external JSONL profile; the core
profile uses independent algebraic identities and committed exact coordinates.
Mode: `if_available`.

Covered operations:
- `ofQAdjoin` for rational, both selected conjugates, and non-unit or
  sign-normalized leading coefficients;
- all tower arithmetic operations over genuine one- and two-level fields,
  including recursive inversion and the `0⁻¹ = 0` convention;
- `adjoin?` for present roots and proper relative extensions;
- `factor?` and `checkFactorization` with content and multiplicity;
- `split?` for degenerate, repeated, and multi-step inputs;
- `flatten?` and both returned coordinate maps.

Covered properties:
- smart constructors preserve the selected absolute embedding and canonical
  mixed-radix dimensions;
- every public factorization reconstructs its input, retains multiplicity, and
  exposes only irreducible checked factors;
- adjoining chooses the unique factor compatible with the fixed embedding;
- splitting returns exactly the expected root count and multiplicities, and
  every returned root satisfies the input relation;
- flattening selects a primitive element of full degree and its two coordinate
  maps are inverse on committed tower generators.

Covered edge cases:
- a linear rational presentation, a negative-leading presentation, both
  conjugates, a non-unit leading coefficient, and the rational tower;
- adjoining a root already present in the tower;
- zero and constant polynomials;
- repeated factors and a polynomial whose roots lie in an intermediate level;
- a reducible absolute polynomial with a nonlinear irreducible relative factor;
- splitting a genuinely relative polynomial over a non-rational base;
- a quartic requiring two genuine splitting extensions.
-/

namespace Hex.NumberTowerConformance

open Hex
open Hex.NumberTower

/-! # Shared fixed-embedding fixtures -/

private def sqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def sqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def sqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, .ofWitness (by decide)⟩, by decide⟩

private def sqrtTwoRoot : SimpleRoot sqrtTwoPoly :=
  SimpleRoot.mk sqrtTwoRep

private def sqrtTwo? : Option (Extension rat) :=
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
      ⟨hirred, by decide⟩
    if hsimple : HasOnlySimpleRoots sqrtTwoPoly then
      some (ofQAdjoin (x := sqrtTwoRoot) hsimple sqrtTwoRep rfl)
    else
      none
  else
    none

private def negSqrtTwoPoly : ZPoly := DensePoly.ofList [2, 0, -1]

private def negSqrtTwoRep : RefinedIsolation negSqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, .ofWitness (by decide)⟩, by decide⟩

private def negSqrtTwo? : Option (Extension rat) :=
  if hirred : ZPoly.isIrreducible negSqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible negSqrtTwoPoly :=
      ⟨hirred, by decide⟩
    if hsimple : HasOnlySimpleRoots negSqrtTwoPoly then
      some (ofQAdjoin (x := SimpleRoot.mk negSqrtTwoRep)
        hsimple negSqrtTwoRep rfl)
    else
      none
  else
    none

private def negativeSqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec (-181) 7, 0, 8⟩

private def negativeSqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨negativeSqrtTwoSquare, .ofWitness (by decide)⟩, by decide⟩

private def negativeSqrtTwo? : Option (Extension rat) :=
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
      ⟨hirred, by decide⟩
    if hsimple : HasOnlySimpleRoots sqrtTwoPoly then
      some (ofQAdjoin (x := SimpleRoot.mk negativeSqrtTwoRep)
        hsimple negativeSqrtTwoRep rfl)
    else
      none
  else
    none

private def sqrtThreeHalvesPoly : ZPoly :=
  DensePoly.ofList [-3, 0, 2]

private def sqrtThreeHalvesSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 157 7, 0, 9⟩

private def sqrtThreeHalvesRep : RefinedIsolation sqrtThreeHalvesPoly :=
  ⟨⟨sqrtThreeHalvesSquare, .ofWitness (by decide)⟩, by decide⟩

private def sqrtThreeHalves? : Option (Extension rat) :=
  if hirred : ZPoly.isIrreducible sqrtThreeHalvesPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtThreeHalvesPoly :=
      ⟨hirred, by decide⟩
    if hsimple : HasOnlySimpleRoots sqrtThreeHalvesPoly then
      some (ofQAdjoin (x := SimpleRoot.mk sqrtThreeHalvesRep)
        hsimple sqrtThreeHalvesRep rfl)
    else
      none
  else
    none

private def threeHalvesPoly : ZPoly := DensePoly.ofList [-3, 2]

private def threeHalvesSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 3 1, 0, 8⟩

private def threeHalvesRep : RefinedIsolation threeHalvesPoly :=
  ⟨⟨threeHalvesSquare, .ofWitness (by decide)⟩, by decide⟩

private def threeHalves? : Option (Extension rat) :=
  if hirred : ZPoly.isIrreducible threeHalvesPoly = true then
    letI : ZPoly.CheckedIrreducible threeHalvesPoly :=
      ⟨hirred, by decide⟩
    if hsimple : HasOnlySimpleRoots threeHalvesPoly then
      some (ofQAdjoin (x := SimpleRoot.mk threeHalvesRep)
        hsimple threeHalvesRep rfl)
    else
      none
  else
    none

private def sqrtThreePoly : ZPoly := DensePoly.ofList [-3, 0, 1]

private def sqrtThreeSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 222 7, 0, 8⟩

private def sqrtThreeRep : RefinedIsolation sqrtThreePoly :=
  ⟨⟨sqrtThreeSquare, .ofWitness (by decide)⟩, by decide⟩

private def sqrtThree? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots sqrtThreePoly then
    some
      { p := sqrtThreePoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk sqrtThreeRep
        rep := sqrtThreeRep
        rep_mk := rfl }
  else
    none

private def fourthRootTwoPoly : ZPoly :=
  DensePoly.ofList [-2, 0, 0, 0, 1]

private def fourthRootTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 77936 16, 0, 17⟩

private def fourthRootTwoRep : RefinedIsolation fourthRootTwoPoly :=
  ⟨⟨fourthRootTwoSquare, .ofWitness (by decide)⟩, by decide⟩

private def fourthRootTwo? : Option AlgebraicRoot :=
  if hsimple : HasOnlySimpleRoots fourthRootTwoPoly then
    some
      { p := fourthRootTwoPoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk fourthRootTwoRep
        rep := fourthRootTwoRep
        rep_mk := rfl }
  else
    none

/-! A cyclotomic retry fixture. With `zeta = exp(2*pi*i/7)`, take
`theta = zeta + zeta^6` and `alpha = zeta^4 - zeta^5 - zeta^6`. The shift
`theta + alpha` has full degree six, but an incompatible conjugate pair makes
the recovery gcd nonlinear; the next signed shift `-1` is recoverable. -/

private def retryThetaPoly : ZPoly :=
  DensePoly.ofList [-1, -2, 1, 1]

private def retryThetaSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 1371068573887 40, 0, 16⟩

private def retryThetaRep : RefinedIsolation retryThetaPoly :=
  ⟨⟨retryThetaSquare, .ofWitness (by decide)⟩, by decide⟩

private def retryTheta? : Option AlgebraicNumber :=
  if hsimple : HasOnlySimpleRoots retryThetaPoly then
    let root : AlgebraicRoot :=
      { p := retryThetaPoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk retryThetaRep
        rep := retryThetaRep
        rep_mk := rfl }
    root.exact?
  else
    none

private def retryAlphaPoly : ZPoly :=
  DensePoly.ofList [29, -1, 15, -1, 1, -1, 1]

private def retryAlphaSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec (-1501032013268545746) 60,
    Dyadic.ofIntWithPrec 1525171791184062904 60, 52⟩

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 1000 in
private def retryAlphaRep : RefinedIsolation retryAlphaPoly :=
  ⟨⟨retryAlphaSquare, .ofWitness (by decide)⟩, by decide⟩

private def retryAlpha? : Option AlgebraicNumber :=
  if hsimple : HasOnlySimpleRoots retryAlphaPoly then
    let root : AlgebraicRoot :=
      { p := retryAlphaPoly
        prim := by rfl
        pos_lc := by decide
        pos_degree := by decide
        squarefree := hsimple
        x := SimpleRoot.mk retryAlphaRep
        rep := retryAlphaRep
        rep_mk := rfl }
    root.exact?
  else
    none

private structure TwoLevel where
  base : Extension rat
  extension : Extension base.tower

private def twoLevel? : Option TwoLevel := do
  let base ← sqrtTwo?
  let root ← sqrtThree?
  let extension ← adjoin? base.tower root
  some ⟨base, extension⟩

private def rationalPoly (coefficients : List Rat) : Poly rat :=
  DensePoly.ofCoeffs (coefficients.toArray.map (ofRat rat))

private def polyCoords {T : NumberTower} (f : Poly T) : Array (Array Rat) :=
  f.toArray.map coeffs

/-! # `ofQAdjoin` -/

-- Typical one-level field: the generator satisfies its defining relation and
-- rationals occupy the constant coordinate.
#guard
    match sqrtTwo? with
    | some extension =>
        extension.tower.dim = 2 && extension.tower.height = 1 &&
          coeffs (extension.gen * extension.gen) = #[2, 0] &&
          coeffs (extension.embed (ofRat rat 5)) = #[5, 0] &&
          extension.root.rep.1.square = sqrtTwoSquare
    | none => false

-- Edge: a linear checked presentation is the rational tower rather than a
-- redundant height-one extension.
#guard
    match threeHalves? with
    | some extension =>
        extension.tower.height = 0 && extension.tower.dim = 1 &&
          coeffs extension.gen = #[3 / 2] &&
          coeffs (extension.embed (ofRat rat 7)) = #[7]
    | none => false

-- Adversarial sign normalization retains the selected positive root while
-- replacing the negative-leading presentation by its positive associate.
#guard
    match negSqrtTwo? with
    | some extension =>
        extension.root.p = sqrtTwoPoly &&
          extension.root.rep.1.square = sqrtTwoSquare &&
          coeffs (extension.gen * extension.gen) = #[2, 0]
    | none => false

-- Adversarial fixed embedding: the negative conjugate must remain negative.
#guard
    match negativeSqrtTwo? with
    | some extension =>
        extension.root.rep.1.square = negativeSqrtTwoSquare &&
          extension.root.rep.1.square != sqrtTwoSquare &&
          coeffs (extension.gen * extension.gen) = #[2, 0]
    | none => false

-- Non-unit leading coefficients exercise rational monic normalization.
#guard
    match sqrtThreeHalves? with
    | some extension =>
        extension.root.rep.1.square = sqrtThreeHalvesSquare &&
          coeffs (extension.gen * extension.gen) = #[3 / 2, 0]
    | none => false

/-! # Tower arithmetic -/

-- Typical arithmetic in a genuine quadratic field, including inversion and
-- division by non-rational elements.
#guard
    match sqrtTwo? with
    | some base =>
        let T := base.tower
        let a := ofRat T 1 + base.gen
        let b := ofRat T 2 - base.gen
        coeffs (a + b) = #[3, 0] &&
          coeffs (a - b) = #[-1, 2] &&
          coeffs (-a) = #[-1, -1] &&
          coeffs (a * b) = #[0, 1] &&
          coeffs a⁻¹ = #[-1, 1] &&
          coeffs (a / b) = #[2, 3 / 2]
    | none => false

-- Edge identities, including both totalized divisions through zero.
#guard
    match sqrtTwo? with
    | some base =>
        let T := base.tower
        let g := base.gen
        coeffs (0 + g) = coeffs g && coeffs (g - 0) = coeffs g &&
          isZero (-(0 : Elem T)) && isZero (0 * g) &&
          coeffs (g * 1) = coeffs g && isZero (0⁻¹ : Elem T) &&
          isZero (g / 0) && isZero (0 / g)
    | none => false

-- Adversarial recursive inversion in `Q(sqrt(2), sqrt(3))`: the inverse of
-- `sqrt(2) + sqrt(3)` is `sqrt(3) - sqrt(2)`.
#guard
    match twoLevel? with
    | some tower =>
        let T := tower.extension.tower
        let sqrtTwo := tower.extension.embed tower.base.gen
        let sqrtThree := tower.extension.gen
        let sum := sqrtTwo + sqrtThree
        let difference := sqrtTwo - sqrtThree
        coeffs (sum + difference) = #[0, 2, 0, 0] &&
          coeffs (sum - difference) = #[0, 0, 2, 0] &&
          coeffs (-sum) = #[0, -1, -1, 0] &&
          coeffs (sum * difference) = #[-1, 0, 0, 0] &&
          coeffs sum⁻¹ = #[0, -1, 1, 0] &&
          coeffs (sum / difference) = #[-5, 0, 0, -2] &&
          !isZero (1 : Elem T)
    | none => false

/-! # `adjoin?` -/

-- Typical proper relative extension.
#guard
    match twoLevel? with
    | some tower =>
        tower.extension.tower.height = 2 &&
          tower.extension.tower.dim = 4 &&
          coeffs (tower.extension.embed tower.base.gen) = #[0, 1, 0, 0] &&
          coeffs (tower.extension.gen * tower.extension.gen) = #[3, 0, 0, 0]
    | none => false

-- Edge: an already-present root produces the identity extension.
#guard
    match sqrtTwo? with
    | some base =>
        match adjoin? base.tower base.root with
        | some identity =>
            identity.tower.height = base.tower.height &&
              identity.tower.dim = base.tower.dim &&
              coeffs identity.gen = coeffs base.gen &&
              coeffs (identity.embed base.gen) = coeffs base.gen
        | none => false
    | none => false

-- Adversarial: `X^4 - 2` is reducible over `Q(sqrt(2))`, but its selected
-- positive fourth root has the nonlinear relative relation `X^2 - sqrt(2)`.
#guard
    match sqrtTwo?, fourthRootTwo? with
    | some base, some root =>
        match adjoin? base.tower root with
        | some extension =>
            extension.tower.dim = 4 && extension.tower.height = 2 &&
              coeffs (extension.gen * extension.gen) = #[0, 1, 0, 0] &&
              extension.root.p = fourthRootTwoPoly
        | none => false
    | _, _ => false

/-! # `factor?` and `checkFactorization` -/

-- Typical rational factorization into two distinct linear factors.
#guard
    let input := rationalPoly [-1, 0, 1]
    match factor? input with
    | some result =>
        coeffs result.scalar = #[1] && result.factors.size = 2 &&
          checkFactorization input result.scalar result.factors &&
          result.factors.all fun entry =>
            entry.2 = 1 && entry.1.degree?.getD 0 = 1 &&
              let root := -(entry.1.coeff 0) / entry.1.leadingCoeff
              coeffs (root * root) = #[1]
    | none => false

-- Edge: zero has zero scalar and no factors.
#guard
    match factor? (0 : Poly rat) with
    | some result =>
        isZero result.scalar && result.factors.isEmpty &&
          checkFactorization 0 result.scalar result.factors
    | none => false

-- Repeated irreducible input retains its Yun multiplicity bucket.
#guard
    let input := rationalPoly [4, 0, -4, 0, 1]
    match factor? input with
    | some result =>
        coeffs result.scalar = #[1] && result.factors.size = 1 &&
          checkFactorization input result.scalar result.factors &&
          result.factors.all fun entry =>
            entry.2 = 2 && polyCoords entry.1 = #[#[-2], #[0], #[1]]
    | none => false

-- Non-unit content is separated into the scalar and reconstructs exactly.
#guard
    let input := rationalPoly [-12, 0, 6]
    match factor? input with
    | some result =>
        coeffs result.scalar = #[6] && result.factors.size = 1 &&
          checkFactorization input result.scalar result.factors &&
          result.factors.all fun entry =>
            entry.2 = 1 && polyCoords entry.1 = #[#[-2], #[0], #[1]]
    | none => false

-- The shift-zero norm over `Q(sqrt(2))` is repeated; recursive Trager must
-- advance before returning the unchanged irreducible quadratic.
#guard
    match sqrtTwo? with
    | some base =>
        let T := base.tower
        let input : Poly T := DensePoly.ofCoeffs #[ofRat T (-3), 0, 1]
        match factor? input with
        | some result =>
            coeffs result.scalar = #[1, 0] && result.factors.size = 1 &&
              checkFactorization input result.scalar result.factors &&
              result.factors.all fun entry =>
                entry.2 = 1 && polyCoords entry.1 = polyCoords input
        | none => false
    | none => false

-- Adversarial recursive Trager case: over `Q(sqrt(2), sqrt(3))`, `X^2 - 3`
-- splits over the intermediate `Q(sqrt(3))`; an absolute-norm-only strategy
-- would see repeated copies.
#guard
    match twoLevel? with
    | some tower =>
        let T := tower.extension.tower
        let input : Poly T := DensePoly.ofCoeffs #[ofRat T (-3), 0, 1]
        match factor? input with
        | some result =>
            result.factors.size = 2 &&
              checkFactorization input result.scalar result.factors &&
              result.factors.all fun entry =>
                entry.2 = 1 && entry.1.degree?.getD 0 = 1 &&
                  let root := -(entry.1.coeff 0) / entry.1.leadingCoeff
                  coeffs (root * root) = #[3, 0, 0, 0]
        | none => false
    | none => false

/-! # `split?` -/

-- Typical quadratic: one adjoining step and both simple roots.
#guard
    let input := rationalPoly [-2, 0, 1]
    match split? input with
    | some result =>
        result.extension.tower.dim = 2 && result.extension.tower.height = 1 &&
          match result.roots with
          | .finite roots =>
              roots.size = 2 && roots.all fun entry =>
                entry.2 = 1 && coeffs (entry.1 * entry.1) = #[2, 0]
          | .all => false
    | none => false

-- Edge: zero has every element as a root; a nonzero constant has no roots.
#guard
    let constant : Poly rat := DensePoly.C (ofRat rat 5)
    match split? 0, split? constant with
    | some zeroResult, some constantResult =>
        match zeroResult.roots, constantResult.roots with
        | .all, .finite roots =>
            zeroResult.extension.tower.height = 0 &&
              constantResult.extension.tower.height = 0 && roots.isEmpty
        | _, _ => false
    | _, _ => false

-- Repeated factors preserve multiplicity through adjoining and refactoring.
#guard
    let input := rationalPoly [4, 0, -4, 0, 1]
    match split? input with
    | some result =>
        match result.roots with
        | .finite roots =>
            result.extension.tower.dim = 2 && roots.size = 2 &&
              roots.all fun entry =>
                entry.2 = 2 && coeffs (entry.1 * entry.1) = #[2, 0]
        | .all => false
    | none => false

-- Relative splitting: over `Q(sqrt(2))`, `X^2 - sqrt(2)` adjoins a fourth
-- root of two, and the same field already contains its negative conjugate.
#guard
    match sqrtTwo? with
    | some base =>
        let T := base.tower
        let input : Poly T := DensePoly.ofCoeffs #[-base.gen, 0, 1]
        match split? input with
        | some result =>
            result.extension.tower.dim = 4 &&
              result.extension.tower.height = 2 &&
              match result.roots with
              | .finite roots =>
                  roots.size = 2 && roots.all fun entry =>
                    entry.2 = 1 &&
                      entry.1 * entry.1 == result.extension.embed base.gen
              | .all => false
        | none => false
    | none => false

-- Adversarial quartic: two genuine adjoining steps and four simple roots.
#guard
    let input := rationalPoly [6, 0, -5, 0, 1]
    match split? input with
    | some result =>
        result.extension.tower.dim = 4 && result.extension.tower.height = 2 &&
          match result.roots with
          | .finite roots =>
              roots.size = 4 && roots.all fun entry =>
                let square := coeffs (entry.1 * entry.1)
                entry.2 = 1 &&
                  (square = #[2, 0, 0, 0] || square = #[3, 0, 0, 0])
          | .all => false
    | none => false

/-! # `flatten?` -/

-- Recovery retry: shift `+1` has full degree but a nonlinear gcd, and the
-- same bounded search continues to the recoverable shift `-1`.
#guard
    match retryTheta?, retryAlpha? with
    | some theta, some alpha =>
        match Flatten.candidateAt? theta alpha 6 1 with
        | some (shift, gamma) =>
            shift = 1 &&
              (Flatten.recoverPairFast? theta alpha gamma shift).isNone &&
              match Flatten.searchRecoveredAux theta alpha 6 1 2 with
              | some recovered => recovered.shift = -1
              | none => false
        | none => false
    | _, _ => false

-- The zero-shift overlapping-field case exercises the total trace fallback at
-- a small degree.
#guard
    match retryTheta? with
    | some theta =>
        match Flatten.recoverPair? theta theta theta 0 with
        | some coordinates =>
            coordinates.1 == theta.toQAdjoin &&
              coordinates.2 == theta.toQAdjoin
        | none => false
    | none => false

-- Edge: the rational tower uses the canonical algebraic zero presentation.
#guard
    match flatten? rat with
    | some flattened =>
        let value := ofRat rat (7 / 3)
        flattened.root.p = ZPoly.X &&
          (flattened.toPrimitive value).coeffs = DensePoly.C (7 / 3) &&
          flattened.fromPrimitive (flattened.toPrimitive value) == value
    | none => false

-- Typical one-level round trip.
#guard
    match sqrtTwo? with
    | some base =>
        match flatten? base.tower with
        | some flattened =>
            flattened.root.p = sqrtTwoPoly &&
              (flattened.toPrimitive base.gen).coeffs =
                DensePoly.ofList [0, 1] &&
              flattened.fromPrimitive (flattened.toPrimitive base.gen) == base.gen
        | none => false
    | none => false

private def sqrtSumPoly : ZPoly := DensePoly.ofList [1, 0, -10, 0, 1]

-- Adversarial two-level round trip: shift zero is non-primitive, while shift
-- one yields `sqrt(2) + sqrt(3)` of full degree four.
#guard
    match twoLevel? with
    | some tower =>
        match flatten? tower.extension.tower with
        | some flattened =>
            let sqrtTwo := tower.extension.embed tower.base.gen
            let sqrtThree := tower.extension.gen
            let twoCoordinate := flattened.toPrimitive sqrtTwo
            let threeCoordinate := flattened.toPrimitive sqrtThree
            flattenShiftCount 4 = 7 &&
              flattened.root.p = sqrtSumPoly &&
              twoCoordinate.coeffs =
                DensePoly.ofList [0, -9 / 2, 0, 1 / 2] &&
              threeCoordinate.coeffs =
                DensePoly.ofList [0, 11 / 2, 0, -1 / 2] &&
              flattened.fromPrimitive twoCoordinate == sqrtTwo &&
              flattened.fromPrimitive threeCoordinate == sqrtThree
        | none => false
    | none => false

end Hex.NumberTowerConformance
