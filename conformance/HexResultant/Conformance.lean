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
  and leaves a remainder smaller than the divisor;
- Brown chains omit zero terms, order unequal-degree inputs, strictly decrease
  after their first two entries, obey the sharp length bound, and are stable
  under extra fuel;
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
