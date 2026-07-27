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
# Raw tower polynomial factorization

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

/-- Fuel-bounded Yun loop. Here `b` is the product of the factors whose
multiplicity is still at least the current index, while `d` is Yun's
derivative correction. Each emitted gcd is the squarefree component of exactly
that multiplicity. -/
@[expose]
def yunAux (levels : List Level)
    (b d : DensePoly (RawElem levels)) (multiplicity fuel : Nat)
    (out : Array (Array (Array Rat) × Nat)) :
    Array (Array (Array Rat) × Nat) :=
  match fuel with
  | 0 => out
  | fuel + 1 =>
      if b = 1 then
        out
      else
        let component := Norm.monic (DensePoly.gcd b d)
        let out := if 0 < component.degree?.getD 0 then
          out.push (polyCoords component, multiplicity)
        else
          out
        let nextB := Norm.monic (b / component)
        let nextC := d / component
        let nextD := nextC - Norm.derivative levels nextB
        yunAux levels nextB nextD (multiplicity + 1) fuel out

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
    let b := Norm.monic (normalized / repeated)
    let c := Norm.derivative levels normalized / repeated
    let d := c - Norm.derivative levels b
    yunAux levels b d 1 (p.size + 1) #[]

/-- Polynomial power used by reconstruction checks, computed by repeated
squaring so high multiplicities do not induce a linear multiplication chain. -/
@[expose]
def polyPow {levels : List Level} (f : DensePoly (RawElem levels)) (n : Nat) :
    DensePoly (RawElem levels) :=
  if n = 0 then
    1
  else
    let half := polyPow f (n / 2)
    let square := half * half
    if n % 2 = 0 then square else square * f
termination_by n
decreasing_by omega

/-- Reconstruct a monic polynomial from raw Yun components. -/
@[expose]
def yunProduct (levels : List Level)
    (components : Array (Array (Array Rat) × Nat)) :
    Array (Array Rat) :=
  polyCoords <| components.foldl
    (fun product component =>
      product * polyPow (rawPoly levels component.1) component.2)
    1

/-- Check that the emitted multiplicities are in strictly increasing order. -/
@[expose]
def yunMultiplicitiesIncrease
    (components : Array (Array (Array Rat) × Nat)) : Bool :=
  (List.range (components.size - 1)).all fun i =>
    (components.getD i (#[], 0)).2 <
      (components.getD (i + 1) (#[], 0)).2

/-- Check that distinct Yun components are pairwise coprime. -/
@[expose]
def yunPairwiseCoprime (levels : List Level)
    (components : Array (Array (Array Rat) × Nat)) : Bool :=
  (List.range components.size).all fun i =>
    (List.range i).all fun j =>
      (DensePoly.gcd (rawPoly levels (components.getD i (#[], 0)).1)
        (rawPoly levels (components.getD j (#[], 0)).1)).size ≤ 1

/-- Self-check a Yun decomposition: multiplicities are positive and strictly
increasing, the monic squarefree components are pairwise coprime, and their
powered product reconstructs the monic input. Zero has the unique empty
decomposition. -/
@[expose]
def checkYun (levels : List Level) (f : Array (Array Rat))
    (components : Array (Array (Array Rat) × Nat)) : Bool :=
  let p := rawPoly levels f
  if p.isZero then
    components.isEmpty
  else
    yunMultiplicitiesIncrease components &&
      components.all (fun component =>
        0 < component.2 &&
          let factor := rawPoly levels component.1
          0 < factor.degree?.getD 0 && factor.leadingCoeff = 1) &&
      yunPairwiseCoprime levels components &&
      components.all (fun component =>
        Norm.isSquarefree levels component.1) &&
      yunProduct levels components = polyCoords (Norm.monic p)

/-- Recover the rational polynomial stored by base-tower raw coordinates. -/
@[expose]
def toRatPoly (f : Array (Array Rat)) : DensePoly Rat :=
  DensePoly.ofCoeffs (f.map fun coefficient => coefficient.getD 0 0)

/-- Convert a rational polynomial back to raw base-tower coordinates. -/
@[expose]
def ofRatPoly (f : DensePoly Rat) : Array (Array Rat) :=
  f.toArray.map fun coefficient => #[coefficient]

/-- Complete factorization of a monic squarefree rational polynomial. The
Berlekamp–Zassenhaus result is accepted only when all multiplicities are one
and the normalized factors reconstruct the input exactly. -/
@[expose]
def factorRat? (input : DensePoly Rat) :
    Option (Array (Array (Array Rat))) :=
  let p := if input.isZero then 0 else
    DensePoly.scale input.leadingCoeff⁻¹ input
  if p.isZero then
    some #[]
  else
    let integer := ZPoly.ratPolyPrimitivePart p
    let factorization := ZPoly.factorize integer
    if factorization.factors.all (fun entry => entry.2 = 1) then
      let factors := factorization.factors.map fun entry =>
        let q := ZPoly.toRatPoly entry.1
        let q := if q.isZero then 0 else DensePoly.scale q.leadingCoeff⁻¹ q
        ofRatPoly q
      let product := factors.foldl
        (fun product factor => product * toRatPoly factor)
        1
      if product = p then some factors else none
    else
      none

/-- The newest generator as a runtime-indexed element. A linear level already
lies in the lower field, so its generator is the negative constant term of its
monic relation. -/
@[expose]
def topGenerator (level : Level) (lower : List Level) :
    RawElem (level :: lower) :=
  if level.degree = 1 then
    -raw (level :: lower) (level.defining.getD 0 #[])
  else
    raw (level :: lower) ((Array.replicate (levelsDim lower) 0).push 1)

/-- Substitute `X - c*alpha` in a current-level polynomial. -/
@[expose]
def shiftTop (level : Level) (lower : List Level)
    (f : Array (Array Rat)) (c : Int) : Array (Array Rat) :=
  let levels := level :: lower
  let delta := raw levels #[(c : Rat)] * topGenerator level lower
  let substitution : DensePoly (RawElem levels) :=
    DensePoly.ofCoeffs #[-delta, 1]
  polyCoords (DensePoly.compose (rawPoly levels f) substitution)

/-- Embed a lower-tail polynomial into the current level. Mixed-radix order
places lower coordinates in the first top-generator block. -/
@[expose]
def embedLower (level : Level) (lower : List Level)
    (f : Array (Array Rat)) : Array (Array Rat) :=
  let levels := level :: lower
  polyCoords <| DensePoly.ofCoeffs <| f.map fun coefficient =>
    raw levels coefficient

/-- Recover current-level factors from irreducible lower factors of a
squarefree Trager norm, then undo the selected generator shift. -/
@[expose]
def recover (level : Level) (lower : List Level)
    (shift : Int) (component : Array (Array Rat))
    (lowerFactors : Array (Array (Array Rat))) :
    Array (Array (Array Rat)) :=
  let levels := level :: lower
  let shifted := rawPoly levels (shiftTop level lower component shift)
  lowerFactors.foldl (fun out lowerFactor =>
    let lifted := rawPoly levels (embedLower level lower lowerFactor)
    let common := Norm.monic (DensePoly.gcd shifted lifted)
    if 0 < common.degree?.getD 0 then
      let unshifted := shiftTop level lower (polyCoords common) (-shift)
      out.push (polyCoords (Norm.monic (rawPoly levels unshifted)))
    else
      out) #[]

/-- Recursive Trager factorization of one monic squarefree component. The
recursion is structural in the tower height; every proper level performs one
bounded one-level norm search and recurses only on the lower tail. -/
@[expose]
def factorSquarefree? : (levels : List Level) → Array (Array Rat) →
    Option (Array (Array (Array Rat)))
  | [], f => factorRat? (toRatPoly f)
  | level :: lower, f => do
      if Norm.isSquarefree (level :: lower) f then
        let (shift, norm) ← Norm.findSquarefreeShift level lower f
        let lowerFactors ← factorSquarefree? lower norm
        let factors := recover level lower shift f lowerFactors
        let p := Norm.monic (rawPoly (level :: lower) f)
        let product := factors.foldl
          (fun product factor => product * rawPoly (level :: lower) factor)
          1
        if factors.all (fun factor =>
            0 < (rawPoly (level :: lower) factor).degree?.getD 0) &&
            product = p then
          some factors
        else
          none
      else
        none

/-- Runtime factorization payload before re-indexing coefficients by a public
`NumberTower`. -/
structure RawFactorization where
  scalar : Array Rat
  factors : Array (Array (Array Rat) × Nat)

/-- Lexicographic order on rational lists. -/
@[expose]
def ratListLess : List Rat → List Rat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a < b then true else if b < a then false else ratListLess as bs

/-- Flatten polynomial coefficient coordinates for canonical sorting. -/
@[expose]
def flattenPoly (f : Array (Array Rat)) : List Rat :=
  f.toList.flatMap Array.toList

/-- Canonical lexicographic factor order. -/
@[expose]
def factorLess (a b : Array (Array Rat)) : Bool :=
  ratListLess (flattenPoly a) (flattenPoly b)

/-- Check that adjacent factors are in strict canonical order. Strictness
ensures each irreducible occurs once, with its multiplicity stored in the
paired natural number. -/
@[expose]
def factorsSorted (factors : Array (Array (Array Rat) × Nat)) : Bool :=
  (List.range (factors.size - 1)).all fun i =>
    factorLess (factors.getD i (#[], 0)).1
      (factors.getD (i + 1) (#[], 0)).1

/-- Multiply a scalar and powered raw factor list. -/
@[expose]
def factorProduct (levels : List Level) (scalar : Array Rat)
    (factors : Array (Array (Array Rat) × Nat)) : Array (Array Rat) :=
  polyCoords <| factors.foldl
    (fun product factor =>
      product * polyPow (rawPoly levels factor.1) factor.2)
    (DensePoly.C (raw levels scalar))

/-- Executable recursive irreducibility checker for a monic squarefree raw
tower polynomial. The rational base delegates to the integer-polynomial checker
shared by rational factorization; proper towers accept exactly a singleton
Trager reconstruction. -/
@[expose]
def isIrreducible (levels : List Level) (f : Array (Array Rat)) : Bool :=
  let p := rawPoly levels f
  0 < p.degree?.getD 0 && p.leadingCoeff = 1 &&
    Norm.isSquarefree levels f &&
    match levels with
    | [] => ZPoly.isIrreducible (ZPoly.ratPolyPrimitivePart (toRatPoly f))
    | _ :: _ =>
        match factorSquarefree? levels f with
        | some factors => factors = #[polyCoords p]
        | none => false

/-- Full executable raw factorization certificate check. At proper tower
levels, “irreducible” means a piece the recursive Trager checker cannot split;
the Mathlib companion supplies the semantic irreducibility theorem. Cheap
reconstruction and canonical-order checks precede recursive replay. -/
@[expose]
def check (levels : List Level) (f : Array (Array Rat)) (scalar : Array Rat)
    (factors : Array (Array (Array Rat) × Nat)) : Bool :=
  factors.all (fun factor =>
      polyCoords (rawPoly levels factor.1) = factor.1) &&
    factorProduct levels scalar factors = f && factorsSorted factors &&
      factors.all (fun factor =>
        0 < factor.2 && isIrreducible levels factor.1)

/-- Produce a canonical factorization candidate with checked Yun
multiplicities and recursive Trager recovery. The public dependent constructor
performs the one full executable certificate replay. -/
@[expose]
def factorRaw? (levels : List Level) (f : Array (Array Rat)) :
    Option RawFactorization := do
  let p := rawPoly levels f
  let scalar := p.leadingCoeff.data
  let components := yunRaw levels f
  if checkYun levels f components then
    let factors ← components.foldlM (fun out component => do
      let irreducibles ← factorSquarefree? levels component.1
      pure <| irreducibles.foldl
        (fun out factor => out.push (factor, component.2)) out) #[]
    let keyed := factors.map fun factor => (flattenPoly factor.1, factor)
    let factors :=
      (keyed.qsort fun a b => ratListLess a.1 b.1).map fun entry => entry.2
    some ⟨scalar, factors⟩
  else
    none

/-! Compiled Yun regressions. -/

private def yunSqrtTwoLevel : Level where
  degree := 2
  defining := #[#[-2], #[0]]
  root := AlgebraicNumber.zero.toRoot

private def factorSqrtThreeLevel : Level where
  degree := 2
  defining := #[#[-3, 0], #[0, 0]]
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

#guard yunRaw [] #[] = #[] && checkYun [] #[] #[]

-- Reconstruction alone is insufficient: splitting one irreducible factor
-- across two multiplicity entries must be rejected as non-coprime.
#guard
    let xSubOne : DensePoly (RawElem []) :=
      DensePoly.ofCoeffs #[raw [] #[-1], raw [] #[1]]
    let f := polyPow xSubOne 3
    !checkYun [] (polyCoords f)
      #[(polyCoords xSubOne, 1), (polyCoords xSubOne, 2)]

-- Positive multiplicity is not enough: Yun components must have positive
-- polynomial degree, so the constant unit is never a component.
#guard
    let one : DensePoly (RawElem []) := 1
    !checkYun [] (polyCoords one) #[(polyCoords one, 1)]

#guard
    let xSqSubTwo : DensePoly Rat := DensePoly.ofList [-2, 0, 1]
    let xSubThree : DensePoly Rat := DensePoly.ofList [-3, 1]
    let input := xSqSubTwo * xSubThree
    match factorRat? input with
    | some factors =>
        factors.size = 2 &&
          factors.foldl
            (fun product factor => product * toRatPoly factor) 1 =
            xSqSubTwo * xSubThree
    | none => false

-- The rational base case is entered only for a squarefree Yun component.
#guard
    let xSubOne : DensePoly Rat := DensePoly.ofList [-1, 1]
    (factorRat? (xSubOne * xSubOne)).isNone

-- Trager's first three shifts collide conjugate sums for `X²-2`; the bounded
-- search reaches shift `2`, recovers both linear factors, and undoes the shift.
#guard
    let levels := [yunSqrtTwoLevel]
    let xSqSubTwo : Array (Array Rat) :=
      #[#[-2, 0], #[0, 0], #[1, 0]]
    match Norm.findSquarefreeShift yunSqrtTwoLevel [] xSqSubTwo,
        factorSquarefree? levels xSqSubTwo with
    | some (shift, _), some factors =>
        let product := factors.foldl
          (fun product factor => product * rawPoly levels factor) 1
        shift = 2 && factors.size = 2 &&
          product = rawPoly levels xSqSubTwo
    | _, _ => false

#guard
    let levels := [yunSqrtTwoLevel]
    let xSqSubThree : Array (Array Rat) :=
      #[#[-3, 0], #[0, 0], #[1, 0]]
    match factorSquarefree? levels xSqSubThree with
    | some factors =>
        factors = #[xSqSubThree]
    | none => false

-- Recursive one-level Trager must retain the intermediate field. Over
-- Q(sqrt(2), sqrt(3)), `X² - 3` splits at the top level even though an
-- absolute norm would obscure that structure with repeated powers.
#guard
    let levels := [factorSqrtThreeLevel, yunSqrtTwoLevel]
    let xSqSubThree : Array (Array Rat) :=
      #[#[-3, 0, 0, 0], #[0, 0, 0, 0], #[1, 0, 0, 0]]
    match factorRaw? levels xSqSubThree with
    | some result =>
        result.factors.size = 2 &&
          check levels xSqSubThree result.scalar result.factors
    | none => false

-- The squarefree entry guard rejects invalid recursive calls before spending
-- the full collision-bound search on resultants.
#guard
    let levels := [yunSqrtTwoLevel]
    let xSubOne : DensePoly (RawElem levels) :=
      rawPoly levels #[#[-1, 0], #[1, 0]]
    (factorSquarefree? levels (polyCoords (polyPow xSubOne 2))).isNone

#guard
    let levels := [yunSqrtTwoLevel]
    let xSqSubTwo : DensePoly (RawElem levels) :=
      rawPoly levels #[#[-2, 0], #[0, 0], #[1, 0]]
    let xSubOne : DensePoly (RawElem levels) :=
      rawPoly levels #[#[-1, 0], #[1, 0]]
    let f := polyPow xSqSubTwo 2 * polyPow xSubOne 3
    match factorRaw? levels (polyCoords f) with
    | some result =>
        result.factors.size = 3 &&
          result.factors.all (fun factor => 0 < factor.2) &&
          check levels (polyCoords f) result.scalar result.factors
    | none => false

-- A factor may appear only once in the canonical certificate; its complete
-- multiplicity belongs in the paired natural number.
#guard
    let xSubOne : Array (Array Rat) := #[#[-1], #[1]]
    let f := polyCoords <| polyPow (rawPoly [] xSubOne) 3
    !check [] f #[1] #[(xSubOne, 1), (xSubOne, 2)]

-- Coordinate padding cannot disguise a duplicate factor from the strict
-- canonical-order check.
#guard
    let xSubOne : Array (Array Rat) := #[#[-1], #[1]]
    let padded : Array (Array Rat) := #[#[-1, 0, 0], #[1]]
    let f := polyCoords <| polyPow (rawPoly [] xSubOne) 3
    !check [] f #[1] #[(padded, 2), (xSubOne, 1)]

end Factor

end Hex.NumberTower
