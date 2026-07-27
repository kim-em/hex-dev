/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower.Embed
public import HexResultant
public meta import HexNumberFieldTower.Embed
public meta import HexResultant

public section

/-!
# One-level tower norms

Trager factorization eliminates only the newest generator at each recursive
step. This module forms `Res_Y(m(Y), g(X - cY))` directly over the lower-tower
coefficient ring, so it neither materializes a determinant nor collapses the
whole tower into one absolute norm.
-/
namespace Hex.NumberTower

namespace Norm

open Arithmetic

/-- Interpret flattened current-tower coordinates as a polynomial in the top
generator, with coefficients that are constant polynomials in `X` over the
lower tower. -/
@[expose]
def liftCoefficient (level : Level) (lower : List Level)
    (a : Array Rat) : DensePoly (DensePoly (RawElem lower)) :=
  let lowerDim := levelsDim lower
  DensePoly.ofCoeffs <| ((List.range level.degree).map fun j =>
    DensePoly.C (raw lower (block a j lowerDim))).toArray

/-- The newest level's monic defining polynomial in the elimination variable,
with coefficients regarded as constant polynomials in `X`. -/
@[expose]
def definingOuter (level : Level) (lower : List Level) :
    DensePoly (DensePoly (RawElem lower)) :=
  DensePoly.ofCoeffs <| (level.defining.map fun a =>
    DensePoly.C (raw lower a)).push (DensePoly.C 1)

/-- Substitute `X - cY` into a polynomial over the current tower, presenting
the result as a polynomial in `Y` over `lower[X]`. -/
@[expose]
def shiftedOuter (level : Level) (lower : List Level)
    (f : Array (Array Rat)) (c : Int) :
    DensePoly (DensePoly (RawElem lower)) :=
  let x : DensePoly (RawElem lower) := DensePoly.monomial 1 1
  let negShift : RawElem lower := raw lower #[(-(c : Rat))]
  let xSubCY : DensePoly (DensePoly (RawElem lower)) :=
    DensePoly.ofCoeffs #[x, DensePoly.C negShift]
  let start : DensePoly (DensePoly (RawElem lower)) ×
      DensePoly (DensePoly (RawElem lower)) := (0, 1)
  (f.foldl (fun state coefficient =>
    (state.1 + liftCoefficient level lower coefficient * state.2,
      state.2 * xSubCY)) start).1

/-- One Trager norm step. Input coefficients are flattened over
`level :: lower`; output coefficients are flattened over `lower`. -/
@[expose]
def oneLevel (level : Level) (lower : List Level)
    (f : Array (Array Rat)) (c : Int) : Array (Array Rat) :=
  (DensePoly.resultant (definingOuter level lower)
    (shiftedOuter level lower f c)).toArray.map RawElem.data

/-- Formal derivative over a runtime-indexed lower tower. -/
@[expose]
def derivative (lower : List Level) (f : DensePoly (RawElem lower)) :
    DensePoly (RawElem lower) :=
  DensePoly.ofCoeffs <| ((List.range (f.size - 1)).map fun i =>
    raw lower <| (f.coeff (i + 1)).data.map fun q =>
      ((i + 1 : Nat) : Rat) * q).toArray

/-- Monic normalization over the runtime-indexed lower tower. -/
@[expose]
def monic (f : DensePoly (RawElem lower)) : DensePoly (RawElem lower) :=
  if f.isZero then 0 else DensePoly.scale f.leadingCoeff⁻¹ f

/-- Executable squarefreeness test over a checked lower tower. -/
@[expose]
def isSquarefree (lower : List Level) (f : Array (Array Rat)) : Bool :=
  let p : DensePoly (RawElem lower) :=
    DensePoly.ofCoeffs (f.map (raw lower))
  !p.isZero && (DensePoly.gcd p (derivative lower p)).size ≤ 1

/-- Number of deterministic Trager shifts required for a top degree `d` and
component degree `m`. -/
@[expose]
def tragerShiftCount (d m : Nat) : Nat :=
  Nat.choose (d * m) 2 + 1

/-- Deterministic signed enumeration `0, 1, -1, 2, -2, ...`. -/
@[expose]
def signedShift (i : Nat) : Int :=
  if i = 0 then
    0
  else if i % 2 = 1 then
    Int.ofNat ((i + 1) / 2)
  else
    -Int.ofNat (i / 2)

/-- Search exactly the finite Trager collision bound and return the first
shift whose one-level norm is squarefree over the lower tower. -/
@[expose]
def findSquarefreeShift (level : Level) (lower : List Level)
    (f : Array (Array Rat)) : Option (Int × Array (Array Rat)) :=
  (List.range (tragerShiftCount level.degree (f.size - 1))).findSome? fun i =>
    let c := signedShift i
    let norm := oneLevel level lower f c
    if isSquarefree lower norm then some (c, norm) else none

/-! Compiled one-level norm regressions over `ℚ(√2)`. -/

private def normSqrtTwoLevel : Level where
  degree := 2
  defining := #[#[-2], #[0]]
  root := AlgebraicNumber.zero.toRoot

private def normSqrtThreeLevel : Level where
  degree := 2
  defining := #[#[-3, 0], #[0, 0]]
  root := AlgebraicNumber.zero.toRoot

#guard
    let xSubSqrtTwo : Array (Array Rat) := #[#[0, -1], #[1, 0]]
    oneLevel normSqrtTwoLevel [] xSubSqrtTwo 0 =
      #[#[-2], #[0], #[1]] &&
    oneLevel normSqrtTwoLevel [] xSubSqrtTwo 1 =
      #[#[-8], #[0], #[1]]

#guard
    let rationalQuadratic : Array (Array Rat) :=
      #[#[-3, 0], #[0, 0], #[1, 0]]
    let norm := oneLevel normSqrtTwoLevel [] rationalQuadratic 0
    norm = #[#[9], #[0], #[-6], #[0], #[1]] &&
      !isSquarefree [] norm

-- The resultant coefficient ring is itself the recursively represented lower
-- tower: eliminating sqrt(3) from a polynomial already over Q(sqrt(2)) uses
-- lower-tower multiplication and exact division.
#guard
    let xSubSqrtThree : Array (Array Rat) :=
      #[#[0, 0, -1, 0], #[1, 0, 0, 0]]
    let xSubSqrtTwo : Array (Array Rat) :=
      #[#[0, -1, 0, 0], #[1, 0, 0, 0]]
    oneLevel normSqrtThreeLevel [normSqrtTwoLevel] xSubSqrtThree 0 =
      #[#[-3, 0], #[0, 0], #[1, 0]] &&
    oneLevel normSqrtThreeLevel [normSqrtTwoLevel] xSubSqrtTwo 0 =
      #[#[2, 0], #[0, -2], #[1, 0]]

#guard
    let xSubSqrtTwo : Array (Array Rat) := #[#[0, -1], #[1, 0]]
    let found := findSquarefreeShift normSqrtTwoLevel [] xSubSqrtTwo
    tragerShiftCount 2 3 = 16 &&
      (List.range 5).map signedShift = [0, 1, -1, 2, -2] &&
      found = some (0, #[#[-2], #[0], #[1]])

end Norm

end Hex.NumberTower
