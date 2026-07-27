/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower.Norm
public import HexBerlekampZassenhaus
public meta import HexNumberFieldTower.Norm
public meta import HexBerlekampZassenhaus

public section

/-!
# Tower polynomial factorization

The first stage of tower factorization is characteristic-zero Yun
decomposition. It runs on the runtime-indexed tower carrier so the same code
serves both public fixed towers and recursive Trager calls on a lower tail.
-/
namespace Hex.NumberTower

namespace Factor

open Arithmetic

/-- Convert raw flattened coefficient arrays to a runtime-indexed tower
polynomial. -/
@[expose]
def rawPoly (levels : List Level) (f : Array (Array Rat)) :
    DensePoly (RawElem levels) :=
  DensePoly.ofCoeffs (f.map (raw levels))

/-- Extract flattened coefficient arrays from a runtime-indexed tower
polynomial. -/
@[expose]
def polyCoords {levels : List Level} (f : DensePoly (RawElem levels)) :
    Array (Array Rat) :=
  f.toArray.map RawElem.data

/-- Fuel-bounded Yun loop. Each emitted component is monic and carries its
positive multiplicity index. -/
@[expose]
def yunAux (levels : List Level)
    (w repeated : DensePoly (RawElem levels)) (multiplicity fuel : Nat)
    (out : Array (Array (Array Rat) × Nat)) :
    Array (Array (Array Rat) × Nat) :=
  match fuel with
  | 0 => out
  | fuel + 1 =>
      if w = 1 then
        out
      else
        let shared := Norm.monic (DensePoly.gcd w repeated)
        let component := Norm.monic (w / shared)
        let out := if 0 < component.degree?.getD 0 then
          out.push (polyCoords component, multiplicity)
        else
          out
        let nextRepeated := Norm.monic (repeated / shared)
        yunAux levels shared nextRepeated (multiplicity + 1) fuel out

/-- Yun squarefree decomposition over raw tower coordinates. Zero and
constants have no positive-degree components. -/
@[expose]
def yunRaw (levels : List Level) (f : Array (Array Rat)) :
    Array (Array (Array Rat) × Nat) :=
  let p := rawPoly levels f
  if p.degree?.getD 0 = 0 then
    #[]
  else
    let normalized := Norm.monic p
    let repeated := Norm.monic
      (DensePoly.gcd normalized (Norm.derivative levels normalized))
    let distinct := Norm.monic (normalized / repeated)
    yunAux levels distinct repeated 1 (p.size + 1) #[]

/-- Polynomial power used by reconstruction checks. -/
@[expose]
def polyPow {levels : List Level} (f : DensePoly (RawElem levels)) : Nat →
    DensePoly (RawElem levels)
  | 0 => 1
  | n + 1 => polyPow f n * f

/-- Reconstruct a monic polynomial from raw Yun components. -/
@[expose]
def yunProduct (levels : List Level)
    (components : Array (Array (Array Rat) × Nat)) :
    Array (Array Rat) :=
  polyCoords <| components.foldl
    (fun product component =>
      product * polyPow (rawPoly levels component.1) component.2)
    1

/-- Self-check a Yun decomposition: multiplicities are positive, every
component is monic and squarefree, and their powered product reconstructs the
monic input. -/
@[expose]
def checkYun (levels : List Level) (f : Array (Array Rat))
    (components : Array (Array (Array Rat) × Nat)) : Bool :=
  let p := rawPoly levels f
  components.all (fun component =>
      0 < component.2 &&
        let factor := rawPoly levels component.1
        !factor.isZero && factor.leadingCoeff = 1 &&
          Norm.isSquarefree levels component.1) &&
    yunProduct levels components = polyCoords (Norm.monic p)

/-- Public Yun decomposition in a fixed tower. -/
@[expose]
def yun (T : NumberTower) (f : Poly T) : Array (Poly T × Nat) :=
  (yunRaw T.levels.toList (f.toArray.map coeffs)).map fun component =>
    (DensePoly.ofCoeffs (component.1.map (ofCoeffs T)), component.2)

/-- Recover the rational polynomial stored by base-tower raw coordinates. -/
@[expose]
def toRatPoly (f : Array (Array Rat)) : DensePoly Rat :=
  DensePoly.ofCoeffs (f.map fun coefficient => coefficient.getD 0 0)

/-- Convert a rational polynomial back to raw base-tower coordinates. -/
@[expose]
def ofRatPoly (f : DensePoly Rat) : Array (Array Rat) :=
  f.toArray.map fun coefficient => #[coefficient]

/-- Complete factorization of a monic rational polynomial. Integer
Berlekamp–Zassenhaus factors are expanded by multiplicity and normalized monic;
the returned array is accepted only after exact rational reconstruction. -/
@[expose]
def factorRat? (f : Array (Array Rat)) :
    Option (Array (Array (Array Rat))) :=
  let input := toRatPoly f
  let p := if input.isZero then 0 else
    DensePoly.scale input.leadingCoeff⁻¹ input
  if p.isZero then
    some #[]
  else
    let integer := ZPoly.ratPolyPrimitivePart p
    let factorization := ZPoly.factorize integer
    let factors := factorization.factors.foldl
      (fun out entry =>
        let q := ZPoly.toRatPoly entry.1
        let q := if q.isZero then 0 else DensePoly.scale q.leadingCoeff⁻¹ q
        (List.range entry.2).foldl (fun out _ => out.push (ofRatPoly q)) out)
      #[]
    let product := factors.foldl
      (fun product factor => product * toRatPoly factor)
      1
    if product = p then some factors else none

/-! Compiled Yun regressions. -/

private def yunSqrtTwoLevel : Level where
  degree := 2
  defining := #[#[-2], #[0]]
  root := AlgebraicNumber.zero.toRoot

#guard
    let xSubOne : DensePoly (RawElem []) :=
      DensePoly.ofCoeffs #[raw [] #[-1], raw [] #[1]]
    let xAddTwo : DensePoly (RawElem []) :=
      DensePoly.ofCoeffs #[raw [] #[2], raw [] #[1]]
    let f := polyPow xSubOne 3 * polyPow xAddTwo 2
    let components := yunRaw [] (polyCoords f)
    components =
      #[(polyCoords xAddTwo, 2), (polyCoords xSubOne, 3)] &&
      checkYun [] (polyCoords f) components

#guard
    let levels := [yunSqrtTwoLevel]
    let xSubSqrtTwo : DensePoly (RawElem levels) :=
      DensePoly.ofCoeffs #[raw levels #[0, -1], raw levels #[1, 0]]
    let xAddSqrtTwo : DensePoly (RawElem levels) :=
      DensePoly.ofCoeffs #[raw levels #[0, 1], raw levels #[1, 0]]
    let f := polyPow xSubSqrtTwo 2 * xAddSqrtTwo
    let components := yunRaw levels (polyCoords f)
    components =
      #[(polyCoords xAddSqrtTwo, 1), (polyCoords xSubSqrtTwo, 2)] &&
      checkYun levels (polyCoords f) components

#guard
    let xSqSubTwo : DensePoly Rat := DensePoly.ofList [-2, 0, 1]
    let xSubThree : DensePoly Rat := DensePoly.ofList [-3, 1]
    let input := ofRatPoly (xSqSubTwo * xSubThree)
    match factorRat? input with
    | some factors =>
        factors.size = 2 &&
          factors.foldl
            (fun product factor => product * toRatPoly factor) 1 =
            xSqSubTwo * xSubThree
    | none => false

end Factor

end Hex.NumberTower
