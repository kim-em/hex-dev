/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexResultant

/-!
Core conformance checks for `HexResultant`.

Oracle: python-flint (`fmpz_poly.resultant` and `fmpz_poly.discriminant`),
with cypari2 as a secondary implementation for the external JSONL profile.
Mode: `if_available`.

Covered operations:
- `exactDiv`, `powNat`, `divExp`, and `DensePoly.divScalar`;
- `DensePoly.pseudoDivMod`;
- `DensePoly.subresultantChain` and the scale-bearing `subresultantRun`;
- `DensePoly.resultant`;
- `DensePoly.disc`.

Covered properties:
- exact quotients, binary powers, and coefficientwise quotients obey their
  independently calculated integer values;
- pseudo-division reconstructs the prescribed leading-coefficient multiple
  and leaves a remainder smaller than the divisor; reconstruction plus that
  bound is unique, and nonzero input scaling obeys the two homogeneity laws;
- coefficient-indexed Sylvester minors reproduce pinned scalar resultants and
  the expected first nontrivial subresultant; their local determinant obeys
  adjacent-transposition sequence parity, arbitrary alternation and column
  updates, consecutive-block rotation, Brown multiplier updates, and the
  generalized polynomials obey left/right homogeneity, the input-swap sign law,
  the Brown--Traub column identity, formal-degree collapse, endpoint
  factorization, pseudo-remainder descent, and exact scalar quotient;
- Brown chains omit zero terms, order unequal-degree inputs, strictly decrease
  after their first two entries, obey the sharp length bound, are stable under
  extra fuel, and satisfy the recursive exactness law on ordered nonzero inputs;
- resultants obey linear evaluation, the degree-product swap sign, common-root
  vanishing, recursive bivariate elimination, and the corrected defective-drop
  scale;
- quadratic discriminants satisfy `b^2 - 4*c`, and repeated roots have
  discriminant zero; the formal derivative-degree correction is exercised in
  positive characteristic.

Covered edge cases:
- zero denominators and zero scalar divisors;
- zero divisors and already-smaller dividends in pseudo-division;
- zero, constant, and common-root inputs;
- defective Brown drops with nonunit exact divisions;
- a recursive dense-polynomial coefficient ring.
-/

namespace Hex.ResultantConformance

open Hex.DensePoly

private def poly (coeffs : List Int) : DensePoly Int :=
  ofList coeffs

private def coeffs (p : DensePoly Int) : List Int :=
  p.toArray.toList

private def chainCoeffs (ps : Array (DensePoly Int)) : List (List Int) :=
  ps.toList.map coeffs

/-- Check the full pseudo-division identity and the strict remainder bound. -/
private def validPseudoDivision (f g : DensePoly Int) : Bool :=
  let qr := pseudoDivMod f g
  scale (powNat g.leadingCoeff (f.size - g.size + 1)) f == qr.1 * g + qr.2 &&
    qr.2.size < g.size

/-- Check strict size descent after the two ordered Brown inputs. -/
private def strictTail (chain : Array (DensePoly Int)) : Bool :=
  (Array.range (chain.size - 2)).all fun offset =>
    let i := offset + 1
    (chain.getD (i + 1) 0).size < (chain.getD i 0).size

/-- Check the public sharp length bound for a nonzero input pair. -/
private def withinChainBound (f g : DensePoly Int) : Bool :=
  decide ((subresultantChain f g).size ≤
    min (f.degree?.getD 0) (g.degree?.getD 0) + 2)

/-! # Exact-division helpers -/

#guard exactDiv (12 : Int) 3 = 4
#guard exactDiv (-21 : Int) 7 = -3
#guard exactDiv (7 : Int) 0 = 0

#guard powNat (3 : Int) 5 = 243
#guard powNat (-2 : Int) 6 = 64
#guard powNat (0 : Int) 0 = 1

#guard divExp (4 : Int) 2 3 = 16
#guard divExp (9 : Int) 3 2 = 27
#guard divExp (7 : Int) 0 0 = 1

#guard coeffs (divScalar (poly [6, -3, 9]) (3 : Int)) = [2, -1, 3]
#guard coeffs (divScalar (poly [6, -3, 9]) (0 : Int)) = []
#guard coeffs (divScalar (poly [12, 0, -6]) (-3 : Int)) = [-4, 0, 2]

/-! # Pseudo-division -/

example (f g q r : DensePoly Int) (hg : g ≠ 0) (hgf : g.size ≤ f.size)
    (hrec : scale (g.leadingCoeff ^ (f.size - g.size + 1)) f = q * g + r)
    (hr : r.size < g.size) : pseudoDivMod f g = (q, r) :=
  pseudoDivMod_unique f g q r hg hgf hrec hr

example (f g : DensePoly Int) {a : Int} (ha : a ≠ 0)
    (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    pseudoDivMod (scale a f) g =
      (scale a (pseudoDivMod f g).1, scale a (pseudoDivMod f g).2) :=
  pseudoDivMod_scale_left f g ha hg hgf

example (f g : DensePoly Int) {a : Int} (ha : a ≠ 0)
    (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    let d := f.size - g.size + 1
    pseudoDivMod f (scale a g) =
      (scale (a ^ (d - 1)) (pseudoDivMod f g).1,
        scale (a ^ d) (pseudoDivMod f g).2) :=
  pseudoDivMod_scale_right f g ha hg hgf

-- Typical nonmonic division: `4*(X^2+1) = (2X-1)*(2X+1)+5`.
#guard
  let f := poly [1, 0, 1]
  let g := poly [1, 2]
  let qr := pseudoDivMod f g
  validPseudoDivision f g && coeffs qr.1 = [-1, 2] && coeffs qr.2 = [5]

-- The public zero-divisor branch is total and returns the dividend unchanged.
#guard
  let f := poly [1, 0, 1]
  let qr := pseudoDivMod f 0
  coeffs qr.1 = [] && qr.2 = f

-- A defective degree drop retains all unused leading-coefficient scaling.
#guard
  let f := poly [0, 0, 0, 1]
  let g := poly [1, 0, 2]
  let qr := pseudoDivMod f g
  validPseudoDivision f g && coeffs qr.1 = [0, 2] && coeffs qr.2 = [0, -2]

-- An already-smaller dividend is the second stable out-of-contract branch.
#guard
  let f := poly [3]
  let g := poly [1, 1]
  pseudoDivMod f g = (0, f)

-- Scaling the dividend scales both outputs by the same nonzero scalar.
#guard
  let f := poly [1, 0, 1]
  let g := poly [1, 2]
  let qr := pseudoDivMod (scale (-3) f) g
  coeffs qr.1 = [3, -6] && coeffs qr.2 = [-15]

-- Scaling the divisor by `a` scales quotient and remainder by `a^(d-1)`
-- and `a^d`, respectively.
#guard
  let f := poly [1, 0, 1]
  let g := poly [1, 2]
  let qr := pseudoDivMod f (scale 3 g)
  coeffs qr.1 = [-3, 6] && coeffs qr.2 = [45]

-- The constant-divisor branch has `d = f.size` and zero remainder.
#guard
  let f := poly [1, 0, 1]
  let g := poly [3]
  let qr := pseudoDivMod f (scale 2 g)
  coeffs qr.1 = [36, 0, 36] && coeffs qr.2 = []

-- Equal-size inputs have `d = 1`, so scaling the divisor leaves the
-- pseudo-quotient unchanged and scales only the remainder.
#guard
  let f := poly [1, 1]
  let g := poly [3, 2]
  let qr := pseudoDivMod f (scale 5 g)
  coeffs qr.1 = [1] && coeffs qr.2 = [-5]

-- Divisor scaling preserves the unused factor across a defective degree drop.
#guard
  let f := poly [0, 0, 0, 1]
  let g := poly [1, 0, 2]
  let qr := pseudoDivMod f (scale (-2) g)
  coeffs qr.1 = [0, -4] && coeffs qr.2 = [0, -8]

-- Nonzero scaling preserves normalized size and scales the leading coefficient.
#guard
  let p := poly [1, 0, -2]
  let q := scale (-3) p
  q.size = p.size && q.leadingCoeff = 6

/-! # Generalized Sylvester minors -/

#guard
  let quadratic := poly [1, 0, 1]
  let linear := poly [-1, 1]
  DensePoly.Subresultant.coeffMinor 0 0 quadratic linear =
      resultant quadratic linear &&
    DensePoly.Subresultant.coeffMinor 1 0 quadratic linear = -1 &&
    DensePoly.Subresultant.coeffMinor 1 1 quadratic linear = 1

#guard
  let cubic := poly [-1, 0, 0, 1]
  let linear := poly [-2, 1]
  let quadratic := poly [1, 0, 1]
  DensePoly.Subresultant.coeffMinor 0 0 cubic linear =
      resultant cubic linear &&
    DensePoly.Subresultant.coeffMinor 0 0 cubic quadratic =
      resultant cubic quadratic

-- Both Sylvester blocks are nonempty and the determinant is genuinely 3×3.
#guard
  let cubic := poly [1, 1, 0, 1]
  let quadratic := poly [-1, 0, 1]
  DensePoly.Subresultant.coeffMinor 1 0 cubic quadratic = 1 &&
    DensePoly.Subresultant.coeffMinor 1 1 cubic quadratic = 2 &&
    DensePoly.Subresultant.coeffMinor 1 2 cubic quadratic = 0 &&
    DensePoly.Subresultant.poly 1 cubic quadratic = poly [1, 2]

-- Degree reversal and equal-degree inputs pin the caller-order convention.
#guard
  let linear := poly [-2, 1]
  let cubic := poly [-1, 0, 0, 1]
  let quadratic1 := poly [1, 0, 1]
  let quadratic2 := poly [2, 1, 1]
  DensePoly.Subresultant.coeffMinor 0 0 linear cubic =
      resultant linear cubic &&
    DensePoly.Subresultant.coeffMinor 0 0 quadratic1 quadratic2 =
      resultant quadratic1 quadratic2

-- The SPEC's two defective Brown examples also pin the scalar minor sign.
#guard
  let f1 := poly [2, 1, 0, 2, 2]
  let g1 := poly [1, 0, 0, 2]
  let f2 := poly [0, 0, 0, 0, -1]
  let g2 := poly [-1, 0, 0, 2]
  DensePoly.Subresultant.coeffMinor 0 0 f1 g1 = 16 &&
    DensePoly.Subresultant.coeffMinor 0 0 f2 g2 = -1

-- Standard subresultants agree with Brown's stored terms at the first regular
-- and defective drops used by the executable regression suite.
#guard
  let quadratic := poly [1, 0, 1]
  let linear := poly [-1, 1]
  let regular := subresultantChain quadratic linear
  let defectiveF := poly [0, 0, 0, 0, -1]
  let defectiveG := poly [-1, 0, 0, 2]
  let defective := subresultantChain defectiveF defectiveG
  DensePoly.Subresultant.poly 0 quadratic linear = regular.getD 2 0 &&
    DensePoly.Subresultant.poly 2 defectiveF defectiveG =
      defective.getD 2 0 &&
    DensePoly.Subresultant.poly 0 defectiveF defectiveG =
      defective.getD 3 0

-- The recursive dense-polynomial coefficient ring exercises bivariate minors.
#guard
  let t : DensePoly Int := poly [0, 1]
  let one : DensePoly Int := 1
  let ySqSubT : DensePoly (DensePoly Int) := ofList [0 - t, 0, one]
  let ySubT : DensePoly (DensePoly Int) := ofList [0 - t, one]
  DensePoly.Subresultant.coeffMinor 0 0 ySqSubT ySubT = t * t - t

example {c : Int} (hc : c ≠ 0) (J : Nat) (f g : DensePoly Int) :
    DensePoly.Subresultant.poly J (scale c f) g =
      scale (c ^ (DensePoly.Subresultant.formalDegree g - J))
        (DensePoly.Subresultant.poly J f g) :=
  DensePoly.Subresultant.poly_scale_left hc J f g

example {c : Int} (hc : c ≠ 0) (J : Nat) (f g : DensePoly Int) :
    DensePoly.Subresultant.poly J f (scale c g) =
      scale (c ^ (DensePoly.Subresultant.formalDegree f - J))
        (DensePoly.Subresultant.poly J f g) :=
  DensePoly.Subresultant.poly_scale_right hc J f g

example (J : Nat) (f g : DensePoly Int) :
    DensePoly.Subresultant.poly J f g =
      scale
        (SubresultantMinor.sign (R := Int)
          ((DensePoly.Subresultant.formalDegree f - J) *
            (DensePoly.Subresultant.formalDegree g - J)))
        (DensePoly.Subresultant.poly J g f) :=
  DensePoly.Subresultant.poly_swap J f g

-- Two nonempty odd-length Sylvester blocks exercise the negative swap sign.
#guard
  let f := poly [1, 0, 1]
  let g := poly [2, 1, 1]
  DensePoly.Subresultant.poly 1 f g =
    scale (-1) (DensePoly.Subresultant.poly 1 g f)

-- Truncating one block to length zero makes input exchange sign-free.
#guard
  let f := poly [1, 1]
  let g := poly [1, 0, 1]
  DensePoly.Subresultant.poly 1 f g =
    DensePoly.Subresultant.poly 1 g f

-- Each input contributes one scalar for every column in its Sylvester block.
#guard
  let cubic := poly [1, 1, 0, 1]
  let quadratic := poly [-1, 0, 1]
  let base := DensePoly.Subresultant.poly 1 cubic quadratic
  let resultantBase := DensePoly.Subresultant.poly 0 cubic quadratic
  let topBase := DensePoly.Subresultant.poly 2 cubic quadratic
  DensePoly.Subresultant.poly 1 (scale (-2) cubic) quadratic = scale (-2) base &&
    DensePoly.Subresultant.poly 1 cubic (scale 3 quadratic) = scale 9 base &&
    DensePoly.Subresultant.poly 0 (scale (-2) cubic) quadratic =
      scale 4 resultantBase &&
    DensePoly.Subresultant.poly 0 cubic (scale 3 quadratic) =
      scale 27 resultantBase &&
    DensePoly.Subresultant.poly 2 (scale (-2) cubic) quadratic = topBase &&
    DensePoly.Subresultant.poly 2 cubic (scale 3 quadratic) = scale 3 topBase

example (M : SubresultantMinor.Square Int 3) (left : Fin 2) :
    SubresultantMinor.det (SubresultantMinor.swapAdjacent M left) =
      0 - SubresultantMinor.det M :=
  SubresultantMinor.det_swapAdjacent M left

example (M : SubresultantMinor.Square Int 3) (swaps : List (Fin 2)) :
    SubresultantMinor.det (SubresultantMinor.applySwaps M swaps) =
      SubresultantMinor.sign (R := Int) swaps.length *
        SubresultantMinor.det M :=
  SubresultantMinor.det_applySwaps M swaps

example (M : SubresultantMinor.Square Int 3) (a b : Fin 3)
    (hab : a ≠ b) (hcol : ∀ i, M i a = M i b) :
    SubresultantMinor.det M = 0 :=
  SubresultantMinor.det_eq_zero_of_col_eq M a b hab hcol

example (M : SubresultantMinor.Square Int 3) (src dst : Fin 3)
    (c : Int) (h : src ≠ dst) :
    SubresultantMinor.det (SubresultantMinor.addCol M src dst c) =
      SubresultantMinor.det M :=
  SubresultantMinor.det_addCol M src dst c h

example (M : SubresultantMinor.Square Int 3) :
    SubresultantMinor.det
        (SubresultantMinor.rotateBlocks M 0 1 1 (by omega)) =
      SubresultantMinor.sign (R := Int) 1 * SubresultantMinor.det M :=
  SubresultantMinor.det_rotateBlocks M 0 1 1 (by omega)

-- An asymmetric matrix pins the adjacent action, odd/even signs, arbitrary
-- duplicate-column vanishing, and arbitrary column update.
#guard
  let rows : List (List Int) := [[1, 2, 3], [0, 1, 4], [5, 6, 0]]
  let M : SubresultantMinor.Square Int 3 :=
    fun i j => (rows.getD i.val []).getD j.val 0
  let moved := SubresultantMinor.applySwaps M [0, 1]
  let rotated := SubresultantMinor.rotateBlocks M 0 1 1 (by omega)
  SubresultantMinor.det M = 1 &&
    SubresultantMinor.det (SubresultantMinor.swapAdjacent M 0) = -1 &&
    SubresultantMinor.det (SubresultantMinor.applySwaps M [0]) = -1 &&
    SubresultantMinor.det moved = 1 &&
    moved 0 0 = 2 && moved 0 1 = 3 && moved 0 2 = 1 &&
    SubresultantMinor.det rotated = -1 &&
    rotated 0 0 = 2 && rotated 0 1 = 1 && rotated 0 2 = 3 &&
    SubresultantMinor.det
      (SubresultantMinor.setCol M 1 (fun i => M i 2)) = 0 &&
    SubresultantMinor.det (SubresultantMinor.addCol M 0 1 7) = 1

example (f g b h : DensePoly Int) (hb : b.size ≤ 2)
    (hh : h = f + b * g) :
    DensePoly.Subresultant.coeffMinorAt 2 1 0 0 f g =
      SubresultantMinor.sign (R := Int) 2 *
        DensePoly.Subresultant.coeffMinorAt 1 2 0 0 g h :=
  DensePoly.Subresultant.coeffMinorAt_addMul 2 1 1 0 0 f g b h
    (by omega) rfl hb hh

example (f g : DensePoly Int) (hgsize : 2 ≤ g.size)
    (hgf : g.size ≤ f.size) :
    DensePoly.Subresultant.poly (g.size - 2) f g =
      scale
        (SubresultantMinor.sign (R := Int) (f.size - g.size + 1))
        (pseudoDivMod f g).2 :=
  DensePoly.Subresultant.poly_prem f g hgsize hgf

example (f g h : DensePoly Int) {c : Int} (hc : c ≠ 0)
    (hg : g ≠ 0) (hh : h ≠ 0) (hgf : g.size ≤ f.size)
    (hp : (pseudoDivMod f g).2 = scale c h) (J : Nat) (hJ : J < h.size) :
    scale
        (g.leadingCoeff ^ ((f.size - g.size + 1) * (g.size - 1 - J)))
        (DensePoly.Subresultant.poly J f g) =
      scale
        (SubresultantMinor.sign (R := Int)
            ((f.size - 1 - J) * (g.size - 1 - J)) *
          g.leadingCoeff ^ (f.size - h.size) *
          c ^ (g.size - 1 - J))
        (DensePoly.Subresultant.poly J g h) :=
  DensePoly.Subresultant.poly_descent f g h hc hg hh hgf hp J hJ

-- Equal input degrees, odd swap parity, `J > 0`, and a remainder whose degree
-- drops below `G` pin the nontrivial Brown column-update regime entrywise.
#guard
  let f := poly [3, 1, 1]
  let g := poly [2, 0, 1]
  let b := poly [-1]
  let h := poly [1, 1]
  let transformed := SubresultantMinor.productCols
    (DensePoly.Subresultant.coeffMatrixAt 2 2 1 0 g f)
      1 0 b 1 (by omega) (by omega)
  let target := DensePoly.Subresultant.coeffMatrixAt 2 2 1 0 g h
  h = f + b * g &&
    transformed 0 0 = target 0 0 && transformed 0 1 = target 0 1 &&
    transformed 1 0 = target 1 0 && transformed 1 1 = target 1 1 &&
    DensePoly.Subresultant.coeffMinorAt 2 2 1 0 f g =
      SubresultantMinor.sign (R := Int) 1 *
        DensePoly.Subresultant.coeffMinorAt 2 2 1 0 g h

-- A four-degree formal collapse pins the full leading-coefficient power, the
-- endpoint factorization, and the resulting exact coefficientwise quotient.
#guard
  let g := poly [1, 0, 0, 2]
  let b := poly [1, 0, 3]
  let h := poly [5, 3]
  let f := h - b * g
  let sub := DensePoly.Subresultant.poly 1 f g
  f.size = 6 && g.size = 4 && b.size = 3 && h.size = 2 &&
    h = f + b * g &&
    sub = scale 48 h &&
    DensePoly.divScalar (scale 48 h) 48 = h

-- A smaller interior-index pin exercises the polynomial transformation before
-- the endpoint, where `J < deg H` and the target remains a subresultant.
#guard
  let g := poly [1, 0, 1]
  let b := poly [-1]
  let h := poly [1, 1]
  let f := h - b * g
  f.size = 3 && g.size = 3 && b.size = 1 && h.size = 2 &&
    h = f + b * g &&
    DensePoly.Subresultant.poly 0 f g =
      scale
        (SubresultantMinor.sign (R := Int) ((2 - 0) * (2 - 0)) *
          g.leadingCoeff ^ (2 - 1))
        (DensePoly.Subresultant.poly 0 g h)

/-! # Brown chain -/

/- The public proof API certifies the same nonzero, descent, and length
properties exercised by the executable guards below. -/
example (f g p : DensePoly Int) (hp : p ∈ subresultantChain f g) : p ≠ 0 :=
  subresultantChain_ne_zero f g p hp

example (f g : DensePoly Int) (i : Nat) (hi : 1 ≤ i)
    (hnext : i + 1 < (subresultantChain f g).size) :
    ((subresultantChain f g).getD (i + 1) 0).size <
      ((subresultantChain f g).getD i 0).size :=
  subresultantChain_size_strict f g i hi hnext

example (f g : DensePoly Int) (hf : f ≠ 0) (hg : g ≠ 0) :
    (subresultantChain f g).size ≤
      min (f.degree?.getD 0) (g.degree?.getD 0) + 2 :=
  subresultantChain_size_le f g hf hg

example (f g : DensePoly Int) (hg : g ≠ 0) (extra : Nat) :
    subresultantOrderedFuel f g (g.size + 1 + extra) =
      subresultantOrdered f g :=
  subresultantOrderedFuel_eq f g hg extra

example (f g : DensePoly Int) (hg : g ≠ 0) (hgf : g.size ≤ f.size) :
    let delta := f.size - g.size
    let h₂ := powNat g.leadingCoeff delta
    let p := (pseudoDivMod f g).2
    if p.isZero then
      h₂ ≠ 0
    else
      let g₃ := scaleImpl (negOnePow (delta + 1)) p
      g₃ ≠ 0 ∧ BrownLaw g g₃ h₂ (g.size + 1) :=
  subresultantOrdered_brownLaw f g hg hgf

#guard
  let f := poly [1, 0, 1]
  let g := poly [-1, 1]
  let chain := subresultantChain f g
  chain.size = 3 && chain.getD 0 0 = f && chain.getD 1 0 = g &&
    chain.all (fun p => !p.isZero) && strictTail chain && withinChainBound f g

#guard
  subresultantChain (0 : DensePoly Int) 0 = #[] &&
    subresultantChain (poly [2, 1]) 0 = #[poly [2, 1]] &&
    subresultantChain 0 (poly [3, 1]) = #[poly [3, 1]]

-- The public wrapper orders a strict degree reversal before entering Brown.
#guard
  let linear := poly [-1, 1]
  let cubic := poly [-1, 0, 0, 1]
  let chain := subresultantChain linear cubic
  chain.getD 0 0 = cubic && chain.getD 1 0 = linear &&
    chain.all (fun p => !p.isZero) && strictTail chain &&
    withinChainBound linear cubic

-- A four-term defective chain exercises two tail descents and a degree gap.
#guard
  let f := poly [0, 0, 0, 0, -1]
  let g := poly [-1, 0, 0, 2]
  let chain := subresultantChain f g
  let publicRun := subresultantOrdered f g
  let extraRun := subresultantOrderedFuel f g (g.size + 8)
  chainCoeffs chain =
      [[0, 0, 0, 0, -1], [-1, 0, 0, 2], [0, -2], [-1]] &&
    chain.all (fun p => !p.isZero) && strictTail chain &&
    withinChainBound f g &&
    extraRun.chain == publicRun.chain && extraRun.scale == publicRun.scale

-- The final polynomial is `4`, while the corrected terminal scale is `16`.
#guard
  let run := subresultantRun
    (poly [2, 1, 0, 2, 2]) (poly [1, 0, 0, 2])
  chainCoeffs run.chain =
    [[2, 1, 0, 2, 2], [1, 0, 0, 2], [4]] && run.scale = 16

/-! # Resultant -/

-- Linear evaluation gives `resultant (X-a) (X-b) = a-b`.
#guard
  resultant (poly [-2, 1]) (poly [-5, 1]) = (-3 : Int) &&
    resultant (poly [3, 1]) (poly [-4, 1]) = -7 &&
    resultant (poly [0, 1]) (poly [-9, 1]) = -9

-- Evaluation, swap sign, and a common root are independent closed-form pins.
#guard
  let q := poly [1, 0, 1]
  let l := poly [-1, 1]
  let xSubTwo := poly [-2, 1]
  let cubic := poly [-1, 0, 0, 1]
  let common := poly [-1, 0, 1]
  resultant q l = (2 : Int) && resultant l q = 2 &&
    resultant xSubTwo cubic = 7 && resultant common l = 0 &&
    resultant q q = 0

-- Default-formal-degree totality conventions.
#guard
  let q := poly [1, 0, 1]
  resultant (0 : DensePoly Int) 0 = (1 : Int) &&
    resultant (C (2 : Int)) (C 3) = 1 &&
    resultant q 0 = 0 && resultant q (C 3) = 9 && resultant q 1 = 1

-- Defective drops exercise both the corrected scale and nonunit divisions.
#guard
  resultant (poly [2, 1, 0, 2, 2]) (poly [1, 0, 0, 2]) = (16 : Int) &&
    resultant (poly [0, 0, 0, 0, -1]) (poly [-1, 0, 0, 2]) = -1

-- Recursive exact division over `DensePoly Int` supports bivariate elimination.
#guard
  let t : DensePoly Int := poly [0, 1]
  let one : DensePoly Int := 1
  let f : DensePoly (DensePoly Int) := ofList [0 - t, 0, one]
  let g : DensePoly (DensePoly Int) := ofList [0 - t, one]
  resultant f g = t * t - t

/-! # Discriminant -/

-- The independently stated quadratic formula is checked on three inputs.
#guard
  disc (poly [2, 3, 1]) = (3 * 3 - 4 * 2 : Int) &&
    disc (poly [-5, -4, 1]) = ((-4) * (-4) - 4 * (-5) : Int) &&
    disc (poly [7, 2, 1]) = (2 * 2 - 4 * 7 : Int)

-- The public total convention fixes every degree-at-most-zero case at one.
#guard
  disc (0 : DensePoly Int) = (1 : Int) &&
    disc (C (0 : Int)) = 1 && disc (C (7 : Int)) = 1

-- Repeated, nonmonic, and cubic cases exercise nontrivial exact quotients.
#guard
  disc (poly [1, -2, 1]) = (0 : Int) &&
    disc (poly [1, 2, 3]) = -8 &&
    disc (poly [-1, 0, 0, 1]) = -27

/- The derivative of `2*X^10 + 3*X` in characteristic five is the constant
`3`, nine degrees below its formal degree. This reaches the leading-coefficient
gap power that is unreachable over the integers. -/
private structure F5 where
  val : Fin 5
deriving DecidableEq

private instance : Zero F5 := ⟨⟨0⟩⟩
private instance : One F5 := ⟨⟨1⟩⟩
private instance (n : Nat) : OfNat F5 n :=
  ⟨{ val := ⟨n % 5, Nat.mod_lt n (by decide)⟩ }⟩
private instance : NatCast F5 :=
  ⟨fun n => { val := ⟨n % 5, Nat.mod_lt n (by decide)⟩ }⟩
private instance : Add F5 := ⟨fun a b => ⟨a.val + b.val⟩⟩
private instance : Sub F5 := ⟨fun a b => ⟨a.val - b.val⟩⟩
private instance : Mul F5 := ⟨fun a b => ⟨a.val * b.val⟩⟩
private instance : Div F5 where
  div a b :=
    let inverse : Fin 5 :=
      match b.val.val with
      | 1 => 1
      | 2 => 3
      | 3 => 2
      | 4 => 4
      | _ => 0
    ⟨a.val * inverse⟩

#guard
  let f : DensePoly F5 := ofList [0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 2]
  disc f = 1

end Hex.ResultantConformance
