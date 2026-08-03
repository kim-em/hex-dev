/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyZ.Kronecker
import HexPolyZ.Mignotte

/-!
Core conformance checks for the `hex-poly-z` integer-polynomial surface.

Oracle: none for the core profile; python-flint/Sage cross-checks are deferred
to external oracle profiles.
Mode: always
Covered operations:
- `ZPoly` as the integer specialization of `DensePoly`
- coefficientwise modular congruence via `ZPoly.congr`
- Bezout-style modular coprimality via `ZPoly.coprimeModP`
- `content`, `primitivePart`, `Primitive`, and primitive square-free
  decomposition
- the Kronecker-substitution product kernel against the schoolbook loop
- Mignotte helpers: `Nat.binom`, `floorSqrt`, `ceilSqrt`, `coeffNormSq`,
  `coeffL2NormBound`, and `mignotteCoeffBound`
Covered properties:
- normalized `ZPoly` values erase trailing zero coefficients while preserving
  internal zeros
- committed congruence fixtures have all checked coefficient differences
  divisible by the modulus
- committed coprimality witnesses reconstruct `1` modulo `p` on checked
  coefficients
- `content * primitivePart` reconstructs committed integer polynomials
- primitive-part fixtures with nonzero content have content `1`
- primitive square-free decomposition removes repeated rational factors after
  primitive-part extraction
- Mignotte coefficient bounds equal `Nat.binom k j * coeffL2NormBound f`
Covered edge cases:
- zero polynomials and all-zero coefficient arrays
- trailing-zero and internal-zero polynomial representations
- modulus `1` congruence and out-of-support coefficient checks
- already primitive and nontrivial-content integer polynomials
- powers of `X`, repeated factors, and nontrivial content before square-free
  normalization
- square-root inputs `0`, nonsquares, and one-below-square adversarial values
- binomial requests with `k = 0` and `k > n`
-/

namespace Hex

namespace ZPoly

-- Typical fixture: `3 - 2x^2 + 7x^10`, exercising the upper end of the
-- `core` profile's polynomial-degree band (SPEC/testing.md § "Profile sizes").
private def zpolyTypical : ZPoly :=
  DensePoly.ofCoeffs #[3, 0, -2, 0, 0, 0, 0, 0, 0, 0, 7]
-- Edge fixture: zero polynomial encoded with a long trailing-zero array.
private def zpolyEdge : ZPoly :=
  DensePoly.ofCoeffs #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- Adversarial fixture: `5x - 7x^3 + 11x^10` with internal and three trailing
-- zeros that normalization must strip.
private def zpolyAdversarial : ZPoly :=
  DensePoly.ofCoeffs #[0, 5, 0, -7, 0, 0, 0, 0, 0, 0, 11, 0, 0]

-- Congruence fixtures (mod 5): each coefficient pair differs by a multiple of 5.
private def congrTypicalLeft : ZPoly :=
  DensePoly.ofCoeffs #[7, -3, 11, 2, -8, 4, 9, -1, 6, 0, 13]
private def congrTypicalRight : ZPoly :=
  DensePoly.ofCoeffs #[2, 12, -4, 7, -3, 9, 4, 4, 1, 5, 8]
private def congrEdgeLeft : ZPoly := DensePoly.ofCoeffs #[4, 0, -9]
private def congrEdgeRight : ZPoly := DensePoly.ofCoeffs #[-2, 13, 5]
-- Adversarial congruence fixtures (mod 12) at degree 10.
private def congrAdversarialLeft : ZPoly :=
  DensePoly.ofCoeffs #[0, 8, 0, -6, 0, 0, 0, 0, 0, 0, 24]
private def congrAdversarialRight : ZPoly :=
  DensePoly.ofCoeffs #[0, -4, 0, 18, 0, 0, 0, 0, 0, 0, 0]

private def congrAt (f g : ZPoly) (m i : Nat) : Bool :=
  ((f.coeff i - g.coeff i) % (m : Int)) == 0

private def congrOn (f g : ZPoly) (m bound : Nat) : Bool :=
  (List.range bound).all (fun i => congrAt f g m i)

-- Typical Bezout (mod 5): `F = 1 + x^10`, `G = 2 + x^10`. The integer identity
-- `(-1)·F + (1)·G = 1` lifts to a Bezout witness modulo any modulus.
private def coprimeTypicalF : ZPoly :=
  DensePoly.ofCoeffs #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
private def coprimeTypicalG : ZPoly :=
  DensePoly.ofCoeffs #[2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
private def coprimeTypicalS : ZPoly := DensePoly.ofCoeffs #[-1]
private def coprimeTypicalT : ZPoly := DensePoly.ofCoeffs #[1]

private def coprimeEdgeF : ZPoly := 0
private def coprimeEdgeG : ZPoly := 1
private def coprimeEdgeS : ZPoly := 0
private def coprimeEdgeT : ZPoly := 1

-- Adversarial Bezout (mod 3): `F = 3 + x^2 + x^10` (sparse, degree 10), `G = 2`
-- (constant unit mod 3). Then `0·F + 2·G = 4 ≡ 1 (mod 3)`.
private def coprimeAdversarialF : ZPoly :=
  DensePoly.ofCoeffs #[3, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]
private def coprimeAdversarialG : ZPoly := DensePoly.ofCoeffs #[2]
private def coprimeAdversarialS : ZPoly := 0
private def coprimeAdversarialT : ZPoly := DensePoly.ofCoeffs #[2]

private def bezoutCongrOn (s t f g : ZPoly) (p bound : Nat) : Bool :=
  congrOn (s * f + t * g) 1 p bound

-- Content / primitive-part fixtures bumped to degree 10.
private def contentZero : ZPoly :=
  DensePoly.ofCoeffs #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
-- Coefficient gcd is `1` (e.g. coefficient at index 0 is `1`).
private def contentPrimitive : ZPoly :=
  DensePoly.ofCoeffs #[1, -2, 3, 0, 0, 5, 0, 0, 7, 0, 11]
-- Coefficient gcd is `gcd(6, 12, 18) = 6`; primitive part divides through.
private def contentNontrivial : ZPoly :=
  DensePoly.ofCoeffs #[-6, 0, 12, 0, 0, 0, 0, 0, 0, 0, 18]
private def contentNontrivialPrimitive : ZPoly :=
  DensePoly.ofCoeffs #[-1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3]
-- Sparse adversarial: gcd is `gcd(14, 21, 7, 35) = 7`.
private def contentAdversarial : ZPoly :=
  DensePoly.ofCoeffs #[-14, 21, 0, -7, 0, 0, 0, 0, 0, 0, 35]
-- `(x - 1)^10`, exercising Q[x] gcd of a perfect tenth power with its
-- derivative `10·(x-1)^9` in the square-free decomposition.
private def squareFreeRepeated : ZPoly :=
  DensePoly.ofCoeffs #[1, -10, 45, -120, 210, -252, 210, -120, 45, -10, 1]
-- `2 · (x - 1)^10`: tests that the content is removed before the rational gcd.
private def squareFreeWithContent : ZPoly :=
  DensePoly.ofCoeffs #[2, -20, 90, -240, 420, -504, 420, -240, 90, -20, 2]
-- `x^10`: pure power of `x`, gcd with `10x^9` is `x^9`, core is `x`.
private def squareFreePowerOfX : ZPoly :=
  DensePoly.ofCoeffs #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
-- `x^10 - 1`: square-free over Q (distinct cyclotomic factors); gcd with the
-- derivative is `1` so the decomposition returns the input unchanged.
private def squareFreeAlreadyCore : ZPoly :=
  DensePoly.ofCoeffs #[-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
-- Negative constant: degenerate degree-zero case for sign normalization.
private def squareFreeNegativeConstant : ZPoly := DensePoly.ofCoeffs #[-2]

#guard zpolyTypical.toArray.toList = [3, 0, -2, 0, 0, 0, 0, 0, 0, 0, 7]
#guard zpolyEdge = (0 : ZPoly)
#guard zpolyAdversarial.toArray.toList = [0, 5, 0, -7, 0, 0, 0, 0, 0, 0, 11]
#guard zpolyTypical.coeff 10 = 7
#guard zpolyEdge.coeff 4 = 0
#guard zpolyAdversarial.coeff 12 = 0

#guard congrOn congrTypicalLeft congrTypicalRight 5 11
#guard congrOn congrEdgeLeft congrEdgeRight 1 5
#guard congrOn congrAdversarialLeft congrAdversarialRight 12 11

example : congr zpolyTypical zpolyTypical 5 := congr_refl zpolyTypical 5
example : congr zpolyEdge zpolyEdge 1 := congr_refl zpolyEdge 1
example : congr zpolyAdversarial zpolyAdversarial 12 := congr_refl zpolyAdversarial 12

#guard bezoutCongrOn coprimeTypicalS coprimeTypicalT coprimeTypicalF coprimeTypicalG 5 11
#guard bezoutCongrOn coprimeEdgeS coprimeEdgeT coprimeEdgeF coprimeEdgeG 7 8
#guard bezoutCongrOn
  coprimeAdversarialS coprimeAdversarialT coprimeAdversarialF coprimeAdversarialG 3 11

example : coprimeModP coprimeEdgeF coprimeEdgeG 7 :=
  coprimeModP_of_bezout coprimeEdgeF coprimeEdgeG coprimeEdgeS coprimeEdgeT 7
    (by
      have h : coprimeEdgeS * coprimeEdgeF + coprimeEdgeT * coprimeEdgeG = (1 : ZPoly) := by
        decide
      simpa [h] using congr_refl (1 : ZPoly) 7)

#guard content contentZero = 0
#guard content contentPrimitive = 1
#guard content contentNontrivial = 6
#guard content contentAdversarial = 7

#guard primitivePart contentZero = (0 : ZPoly)
#guard primitivePart contentPrimitive = contentPrimitive
#guard primitivePart contentNontrivial = contentNontrivialPrimitive
#guard (primitivePart contentAdversarial).toArray.toList =
  [-2, 3, 0, -1, 0, 0, 0, 0, 0, 0, 5]

#guard DensePoly.scale (content contentZero) (primitivePart contentZero) = contentZero
#guard DensePoly.scale (content contentPrimitive) (primitivePart contentPrimitive) =
  contentPrimitive
#guard DensePoly.scale (content contentNontrivial) (primitivePart contentNontrivial) =
  contentNontrivial
#guard DensePoly.scale (content contentAdversarial) (primitivePart contentAdversarial) =
  contentAdversarial

#guard content (primitivePart contentPrimitive) = 1
#guard content (primitivePart contentNontrivial) = 1
#guard content (primitivePart contentAdversarial) = 1

-- `(1/2)·(1 - x^10)` clears denominators to `1 - x^10`; primitive normalization
-- flips the sign of the leading coefficient, yielding `x^10 - 1`.
#guard ratPolyPrimitivePart
    (DensePoly.ofCoeffs
      (#[(1 : Rat) / 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, (-1 : Rat) / 2])) =
  DensePoly.ofCoeffs #[-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
#guard (primitiveSquareFreeDecomposition squareFreeRepeated).primitive =
  squareFreeRepeated
#guard (primitiveSquareFreeDecomposition squareFreeRepeated).squareFreeCore =
  DensePoly.ofCoeffs #[-1, 1]
-- `(x - 1)^9` is the rational gcd of `(x - 1)^10` and `10·(x - 1)^9`.
#guard (primitiveSquareFreeDecomposition squareFreeRepeated).repeatedPart =
  DensePoly.ofCoeffs #[-1, 9, -36, 84, -126, 126, -84, 36, -9, 1]
#guard (primitiveSquareFreeDecomposition squareFreeWithContent).primitive =
  squareFreeRepeated
#guard (primitiveSquareFreeDecomposition squareFreeWithContent).squareFreeCore =
  DensePoly.ofCoeffs #[-1, 1]
#guard (primitiveSquareFreeDecomposition squareFreePowerOfX).squareFreeCore =
  DensePoly.ofCoeffs #[0, 1]
#guard (primitiveSquareFreeDecomposition squareFreeAlreadyCore).squareFreeCore =
  squareFreeAlreadyCore
#guard (primitiveSquareFreeDecomposition squareFreeNegativeConstant).squareFreeCore =
  (1 : ZPoly)
#guard squareFreeCore squareFreeRepeated = DensePoly.ofCoeffs #[-1, 1]

example : Primitive (primitivePart contentPrimitive) := by
  change content (primitivePart contentPrimitive) = 1
  decide

-- `Nat.binom 12 5 = 792`: typical-degree request near the SPEC ceiling for the
-- core polynomial-degree band.
#guard Nat.binom 12 5 = 792
#guard Nat.binom 10 0 = 1
#guard Nat.binom 7 12 = 0

-- `1000 = floorSqrt (10^6)`; `9999 = floorSqrt (10^8 - 1)` since
-- `9999^2 = 99_980_001 < 99_999_999 < 100_000_000 = 10000^2`.
#guard floorSqrt 1000000 = 1000
#guard floorSqrt 0 = 0
#guard floorSqrt 99999999 = 9999

#guard ceilSqrt 1000000 = 1000
#guard ceilSqrt 0 = 0
#guard ceilSqrt 99999999 = 10000

-- `[3, 4, 0, …, 12]`: `9 + 16 + 144 = 169 = 13^2`.
#guard coeffNormSq (DensePoly.ofCoeffs #[3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 12]) = 169
#guard coeffNormSq (0 : ZPoly) = 0
-- `[-6, 0, 8, 0, …, 24]`: `36 + 64 + 576 = 676 = 26^2`.
#guard coeffNormSq (DensePoly.ofCoeffs #[-6, 0, 8, 0, 0, 0, 0, 0, 0, 0, 24]) = 676

#guard coeffL2NormBound (DensePoly.ofCoeffs #[3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 12]) = 13
#guard coeffL2NormBound (0 : ZPoly) = 0
#guard coeffL2NormBound (DensePoly.ofCoeffs #[-6, 0, 8, 0, 0, 0, 0, 0, 0, 0, 24]) = 26

-- Typical Mignotte: `Nat.binom 8 4 · 13 = 70 · 13 = 910`.
#guard mignotteCoeffBound (DensePoly.ofCoeffs #[3, 4, 0, 0, 0, 0, 0, 0, 0, 0, 12]) 8 4 = 910
#guard mignotteCoeffBound (0 : ZPoly) 8 4 = 0
-- Adversarial Mignotte: `Nat.binom 12 6 · 26 = 924 · 26 = 24024`.
#guard mignotteCoeffBound
    (DensePoly.ofCoeffs #[-6, 0, 8, 0, 0, 0, 0, 0, 0, 0, 24]) 12 6 = 24024
#guard mignotteCoeffBound
    (DensePoly.ofCoeffs #[-6, 0, 8, 0, 0, 0, 0, 0, 0, 0, 24]) 12 6 =
  Nat.binom 12 6 *
    coeffL2NormBound (DensePoly.ofCoeffs #[-6, 0, 8, 0, 0, 0, 0, 0, 0, 0, 24])

/-! # The Kronecker product kernel against the schoolbook loop

`mulKroneckerAt_eq` already proves these equal for all inputs. This block is an
executable cross-check of the *compiled* path: the kernel reads slot widths
through `Nat.log2` and shifts through `Nat.shiftLeft` / `Nat.shiftRight`, all of
which are `@[extern]`, so their compiled behaviour is outside what the proof
sees. Cutoffs of `0` force the substitution at every non-zero shape; a zero operand
still short-circuits before packing, which is the case the first sweep
entry covers. -/

/-- Deterministic signed coefficients spanning several magnitudes. -/
private def kernelCoeff (n i salt : Nat) : Int :=
  let raw := Int.ofNat (((i + 3) * (salt + 7) + (i + 1) * (i + 5) * 11 + n * 13) % 1009 + 1)
  raw * Int.ofNat (2 ^ (salt % 5 * 17)) * (if (i + salt) % 3 = 0 then -1 else 1)

private def kernelPoly (n salt : Nat) : ZPoly :=
  DensePoly.ofCoeffs ((List.range n).map (fun i => kernelCoeff n i salt)).toArray

/-- Both kernels agree on every swept shape: sizes straddling the production
size cutoff of 24 and down to the zero and constant polynomials, coefficient
magnitudes straddling the bit cutoff, unbalanced operands, and both operand
orders. -/
private def kernelAgrees : Bool :=
  ([0, 1, 2, 3, 8, 16, 23, 24, 25, 32, 40] : List Nat).all fun n =>
    ([0, 1, 2, 3, 4] : List Nat).all fun salt =>
      let p := kernelPoly n salt
      let q := kernelPoly (n + 3) (salt + 1)
      (mulKroneckerAt 0 0 p q == p * q)
        && (mulKroneckerAt 0 0 q p == q * p)
        && (mulKronecker p q == p * q)

#guard kernelAgrees

/-- Coefficients straddling a power of two, where an `@[extern]` `Nat.log2`
disagreeing with its Lean definition by one would change the slot width. -/
private def boundaryPoly (k i : Nat) : ZPoly :=
  DensePoly.ofCoeffs ((List.range 30).map fun j =>
    let base : Int := Int.ofNat (2 ^ (k + j % 3))
    let raw := base + Int.ofNat ((j + i) % 3) - 1
    if (j + i) % 2 = 0 then raw else -raw).toArray

/-- The kernels agree on coefficients at `2^k - 1`, `2^k` and `2^k + 1`, for
widths spanning the unboxed-`Int` boundary. -/
private def kernelAgreesOnBoundaries : Bool :=
  ([1, 15, 16, 17, 19, 20, 21, 31, 32, 61, 62, 63, 64, 92, 127, 128] : List Nat).all fun k =>
    ([0, 1] : List Nat).all fun i =>
      let p := boundaryPoly k i
      let q := boundaryPoly (k + 1) (i + 1)
      (mulKroneckerAt 0 0 p q == p * q) && (mulKronecker p q == p * q)

#guard kernelAgreesOnBoundaries

end ZPoly

end Hex
