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

/-- Check that the emitted multiplicities are in strictly increasing order. -/
@[expose]
def yunMultiplicitiesIncrease
    (components : Array (Array (Array Rat) × Nat)) : Bool :=
  (List.range (components.size - 1)).all fun i =>
    components[i]!.2 < components[i + 1]!.2

/-- Check that distinct Yun components are pairwise coprime. -/
@[expose]
def yunPairwiseCoprime (levels : List Level)
    (components : Array (Array (Array Rat) × Nat)) : Bool :=
  (List.range components.size).all fun i =>
    (List.range i).all fun j =>
      (DensePoly.gcd (rawPoly levels components[i]!.1)
        (rawPoly levels components[j]!.1)).size ≤ 1

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
    components.all (fun component =>
        0 < component.2 &&
          let factor := rawPoly levels component.1
          !factor.isZero && factor.leadingCoeff = 1 &&
            Norm.isSquarefree levels component.1) &&
      yunMultiplicitiesIncrease components &&
      yunPairwiseCoprime levels components &&
      yunProduct levels components = polyCoords (Norm.monic p)

/-- Checked Yun decomposition in a fixed tower. -/
@[expose]
def yun? (T : NumberTower) (f : Poly T) : Option (Array (Poly T × Nat)) :=
  let input := f.toArray.map coeffs
  let components := yunRaw T.levels.toList input
  if checkYun T.levels.toList input components then
    some <| components.map fun component =>
      (DensePoly.ofCoeffs (component.1.map (ofCoeffs T)), component.2)
  else
    none

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

/-- Runtime factorization payload before re-indexing coefficients by a public
`NumberTower`. -/
structure RawFactorization where
  scalar : Array Rat
  factors : Array (Array (Array Rat) × Nat)
deriving DecidableEq

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
    factorLess factors[i]!.1 factors[i + 1]!.1

/-- Multiply a scalar and powered raw factor list. -/
@[expose]
def factorProduct (levels : List Level) (scalar : Array Rat)
    (factors : Array (Array (Array Rat) × Nat)) : Array (Array Rat) :=
  polyCoords <| factors.foldl
    (fun product factor =>
      product * polyPow (rawPoly levels factor.1) factor.2)
    (DensePoly.C (raw levels scalar))

/-- Executable recursive irreducibility checker for a monic squarefree raw
tower polynomial. It reruns Trager factorization and accepts exactly a
singleton reconstruction. -/
@[expose]
def isIrreducible (levels : List Level) (f : Array (Array Rat)) : Bool :=
  let p := rawPoly levels f
  0 < p.degree?.getD 0 && p.leadingCoeff = 1 &&
    Norm.isSquarefree levels f &&
    match factorSquarefree? levels f with
    | some factors => factors = #[polyCoords p]
    | none => false

/-- Full executable raw factorization certificate check. -/
@[expose]
def check (levels : List Level) (f : Array (Array Rat)) (scalar : Array Rat)
    (factors : Array (Array (Array Rat) × Nat)) : Bool :=
  factors.all (fun factor => 0 < factor.2 && isIrreducible levels factor.1) &&
    factorsSorted factors && factorProduct levels scalar factors = f

/-- Complete factorization with Yun multiplicities and recursive Trager
recovery. Every candidate is sorted and replayed through the full executable
certificate check before it is returned. -/
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
    let factors := factors.qsort fun a b => factorLess a.1 b.1
    if check levels f scalar factors then
      some ⟨scalar, factors⟩
    else
      none
  else
    none

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
    yunRaw [] #[] = #[] && checkYun [] #[] #[] &&
      match yun? rat (0 : Poly rat) with
      | some components => components.isEmpty
      | none => false

-- Reconstruction alone is insufficient: splitting one irreducible factor
-- across two multiplicity entries must be rejected as non-coprime.
#guard
    let xSubOne : DensePoly (RawElem []) :=
      DensePoly.ofCoeffs #[raw [] #[-1], raw [] #[1]]
    let f := polyPow xSubOne 3
    !checkYun [] (polyCoords f)
      #[(polyCoords xSubOne, 1), (polyCoords xSubOne, 2)]

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

-- Trager's first two shifts collide conjugate sums for `X²-2`; the bounded
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

end Factor

/-- Reconstruct and recursively certify a proposed public factorization. -/
@[expose]
def checkFactorization {T : NumberTower} (f : Poly T) (scalar : Elem T)
    (factors : Array (Poly T × Nat)) : Bool :=
  Factor.check T.levels.toList
    (f.toArray.map coeffs) (coeffs scalar)
    (factors.map fun factor =>
      (factor.1.toArray.map coeffs, factor.2))

/-- A checked complete factorization in a fixed tower. -/
structure Factorization (T : NumberTower) (f : Poly T) where
  scalar : Elem T
  factors : Array (Poly T × Nat)
  checked : checkFactorization f scalar factors = true

/-- Complete irreducible factorization with multiplicity. -/
def factor? (T : NumberTower) (f : Poly T) : Option (Factorization T f) := do
  let raw ← Factor.factorRaw? T.levels.toList (f.toArray.map coeffs)
  let scalar := ofCoeffs T raw.scalar
  let factors := raw.factors.map fun factor =>
    (DensePoly.ofCoeffs (factor.1.map (ofCoeffs T)), factor.2)
  if h : checkFactorization f scalar factors then
    some ⟨scalar, factors, h⟩
  else
    none

/-! Compiled public dependent-result regression. -/

private def factorSqrtTwoPoly : ZPoly := DensePoly.ofList [-2, 0, 1]

private def factorSqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def factorSqrtTwoRep : RefinedIsolation factorSqrtTwoPoly :=
  ⟨⟨factorSqrtTwoSquare, by decide⟩, by decide⟩

private def factorSqrtTwoRoot : SimpleRoot factorSqrtTwoPoly :=
  SimpleRoot.mk factorSqrtTwoRep

#guard
    if hirred : ZPoly.isIrreducible factorSqrtTwoPoly = true then
      letI : ZPoly.CheckedIrreducible factorSqrtTwoPoly :=
        ⟨hirred, by decide⟩
      if hsimple : HasOnlySimpleRoots factorSqrtTwoPoly then
        let extension := ofQAdjoin (x := factorSqrtTwoRoot)
          hsimple factorSqrtTwoRep rfl
        let f : Poly extension.tower := DensePoly.ofCoeffs
          #[ofRat extension.tower (-2), 0, 1]
        match factor? extension.tower f,
            factor? extension.tower 0,
            factor? extension.tower (DensePoly.C (ofRat extension.tower 5)) with
        | some result, some zeroResult, some constantResult =>
            result.factors.size = 2 &&
              coeffs result.scalar = #[1, 0] &&
              zeroResult.factors.isEmpty &&
              isZero zeroResult.scalar &&
              constantResult.factors.isEmpty &&
              coeffs constantResult.scalar = #[5, 0]
        | _, _, _ => false
      else
        false
    else
      false

end Hex.NumberTower
