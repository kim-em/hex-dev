/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower.Basic
public meta import HexNumberFieldTower.Basic

public section

/-!
# Mixed-radix tower arithmetic

Multiplication recursively convolves blocks over the lower tower and reduces
from the highest top-generator power using the stored monic relation.
Inversion performs polynomial extended gcd at the top level, with coefficient
inversion recursively supplied by the lower tower. At the rational base the
same recursion is ordinary rational inversion.
-/
namespace Hex.NumberTower

namespace Arithmetic

/-- Fixed-width rational coordinates, padding with zero and truncating excess
entries. -/
@[expose]
def fixedCoeffs (n : Nat) (coefficients : Array Rat) : Array Rat :=
  (Vector.ofFn fun i : Fin n => coefficients.getD i.val 0).toArray

/-- Fixed-width coordinate addition. -/
@[expose]
def addCoords (n : Nat) (a b : Array Rat) : Array Rat :=
  (Vector.ofFn fun i : Fin n => a.getD i.val 0 + b.getD i.val 0).toArray

/-- Fixed-width coordinate subtraction. -/
@[expose]
def subCoords (n : Nat) (a b : Array Rat) : Array Rat :=
  (Vector.ofFn fun i : Fin n => a.getD i.val 0 - b.getD i.val 0).toArray

/-- Fixed-width coordinate negation. -/
@[expose]
def negCoords (n : Nat) (a : Array Rat) : Array Rat :=
  (Vector.ofFn fun i : Fin n => -a.getD i.val 0).toArray

/-- One mixed-radix block. -/
@[expose]
def block (a : Array Rat) (index width : Nat) : Array Rat :=
  (Vector.ofFn fun i : Fin width => a.getD (index * width + i.val) 0).toArray

/-- Flatten a fixed number of equally wide coordinate blocks. -/
@[expose]
def flattenBlocks (count width : Nat) (blocks : Array (Array Rat)) : Array Rat :=
  if width = 0 then
    #[]
  else
    (Vector.ofFn fun i : Fin (count * width) =>
      (blocks.getD (i.val / width) #[]).getD (i.val % width) 0).toArray

/-- Recursive mixed-radix multiplication on top-first raw level data. -/
@[expose]
def mulCoords : (levels : List Level) → Array Rat → Array Rat → Array Rat
  | [], a, b => #[a.getD 0 0 * b.getD 0 0]
  | level :: lower, a, b =>
      let d := level.degree
      let lowerDim := levelsDim lower
      if d = 0 then
        #[]
      else
        let zeroBlock : Array Rat := Array.replicate lowerDim 0
        let work := Array.replicate (2 * d - 1) zeroBlock
        let convolved := (List.range d).foldl
          (fun work i => (List.range d).foldl
            (fun work j =>
              let product := mulCoords lower
                (block a i lowerDim) (block b j lowerDim)
              let k := i + j
              work.set! k (addCoords lowerDim work[k]! product))
            work)
          work
        let reduced := (List.range (d - 1)).foldl
          (fun work offset =>
            let k := 2 * d - 2 - offset
            let high := work[k]!
            (List.range d).foldl
              (fun work j =>
                let relation := level.defining.getD j zeroBlock
                let correction := mulCoords lower high relation
                let target := k - d + j
                work.set! target
                  (subCoords lowerDim work[target]! correction))
              work)
          convolved
        flattenBlocks d lowerDim (reduced.take d)

/-- Dynamically indexed tower coefficient used internally when an algorithm
recurses through runtime level data rather than a dependent `NumberTower`.
The `raw` helper normalizes to the represented mixed-radix dimension. -/
structure RawElem (levels : List Level) where
  data : Array Rat

@[expose]
def raw (levels : List Level) (data : Array Rat) : RawElem levels :=
  .mk (fixedCoeffs (levelsDim levels) data)

instance (levels : List Level) : DecidableEq (RawElem levels) :=
  fun a b =>
    match decEq a.data.toList b.data.toList with
    | isTrue h => isTrue (by cases a; cases b; simpa using h)
    | isFalse h => isFalse fun hab => h (by simp [hab])

instance (levels : List Level) : Zero (RawElem levels) :=
  ⟨raw levels #[]⟩

instance (levels : List Level) : One (RawElem levels) :=
  ⟨raw levels #[1]⟩

instance (levels : List Level) : Add (RawElem levels) :=
  ⟨fun a b => .mk (addCoords (levelsDim levels) a.data b.data)⟩

instance (levels : List Level) : Sub (RawElem levels) :=
  ⟨fun a b => .mk (subCoords (levelsDim levels) a.data b.data)⟩

instance (levels : List Level) : Neg (RawElem levels) :=
  ⟨fun a => .mk (negCoords (levelsDim levels) a.data)⟩

instance (levels : List Level) : Mul (RawElem levels) :=
  ⟨fun a b => .mk (mulCoords levels a.data b.data)⟩

/-- Recursive inverse coordinates. The zero convention is inherited at every
level; defensive nonconstant/zero gcd branches are unreachable for a tower
created by the checked constructors. -/
def invCoords : (levels : List Level) → Array Rat → Array Rat
  | [], a => #[if a.getD 0 0 = 0 then 0 else (a.getD 0 0)⁻¹]
  | level :: lower, a =>
      let lowerDim := levelsDim lower
      let d := level.degree
      if (fixedCoeffs (d * lowerDim) a).all (fun q => q = 0) then
        Array.replicate (d * lowerDim) 0
      else
        letI : Inv (RawElem lower) :=
          ⟨fun x => raw lower (invCoords lower x.data)⟩
        letI : Div (RawElem lower) := ⟨fun x y => x * y⁻¹⟩
        let value : DensePoly (RawElem lower) :=
          DensePoly.ofCoeffs <| ((List.range d).map fun i =>
            raw lower (block a i lowerDim)).toArray
        let defining : DensePoly (RawElem lower) :=
          DensePoly.ofCoeffs <| ((List.range d).map fun i =>
            raw lower (level.defining.getD i #[])).toArray.push 1
        let result := DensePoly.xgcdLeft value defining
        if result.gcd.size = 1 then
          let c := result.gcd.leadingCoeff
          if c = 0 then
            Hex.panicWith (Array.replicate (d * lowerDim) 0)
              "NumberTower.inv: zero constant gcd"
          else
            let normalized := DensePoly.scale c⁻¹ result.left
            flattenBlocks d lowerDim <| ((List.range d).map fun i =>
              (normalized.coeff i).data).toArray
        else
          Hex.panicWith (Array.replicate (d * lowerDim) 0)
            "NumberTower.inv: nonconstant gcd"

instance (levels : List Level) : Inv (RawElem levels) :=
  ⟨fun a => raw levels (invCoords levels a.data)⟩

instance (levels : List Level) : Div (RawElem levels) :=
  ⟨fun a b => a * b⁻¹⟩

private def sqrtTwoLevel : Level where
  degree := 2
  defining := #[#[-2], #[0]]
  root := AlgebraicNumber.zero.toRoot

private def sqrtThreeLevel : Level where
  degree := 2
  defining := #[#[-3, 0], #[0, 0]]
  root := AlgebraicNumber.zero.toRoot

-- One- and two-level arithmetic is independent of the stored complex root;
-- the checked constructor verifies that embedding datum separately.
#guard
    mulCoords [sqrtTwoLevel] #[0, 1] #[0, 1] = #[2, 0] &&
      invCoords [sqrtTwoLevel] #[0, 1] = #[0, 1 / 2]

#guard
    let levels := [sqrtThreeLevel, sqrtTwoLevel]
    let sqrtTwo : Array Rat := #[0, 1, 0, 0]
    let sqrtThree : Array Rat := #[0, 0, 1, 0]
    let sqrtSix := mulCoords levels sqrtTwo sqrtThree
    mulCoords levels sqrtThree sqrtThree = #[3, 0, 0, 0] &&
      sqrtSix = #[0, 0, 0, 1] &&
      invCoords levels sqrtSix = #[0, 0, 0, 1 / 6]

end Arithmetic

/-- Boolean zero test on fixed mixed-radix coordinates. -/
@[expose]
def isZero {T : NumberTower} (a : Elem T) : Bool :=
  (coeffs a).all fun q => q = 0

/-- Additive identity. -/
@[expose]
def zero (T : NumberTower) : Elem T :=
  ofCoeffs T #[]

instance {T : NumberTower} : Zero (Elem T) := ⟨zero T⟩

/-- Multiplicative identity. -/
@[expose]
def one (T : NumberTower) : Elem T :=
  ofCoeffs T #[1]

instance {T : NumberTower} : One (Elem T) := ⟨one T⟩

/-- Coordinatewise addition. -/
@[expose]
def add {T : NumberTower} (a b : Elem T) : Elem T :=
  ofCoeffs T (Arithmetic.addCoords T.dim (coeffs a) (coeffs b))

instance {T : NumberTower} : Add (Elem T) := ⟨add⟩

/-- Coordinatewise subtraction. -/
@[expose]
def sub {T : NumberTower} (a b : Elem T) : Elem T :=
  ofCoeffs T (Arithmetic.subCoords T.dim (coeffs a) (coeffs b))

instance {T : NumberTower} : Sub (Elem T) := ⟨sub⟩

/-- Coordinatewise additive inverse. -/
@[expose]
def neg {T : NumberTower} (a : Elem T) : Elem T :=
  ofCoeffs T (Arithmetic.negCoords T.dim (coeffs a))

instance {T : NumberTower} : Neg (Elem T) := ⟨neg⟩

/-- Recursive convolution and monic reduction. -/
@[expose]
def mul {T : NumberTower} (a b : Elem T) : Elem T :=
  ofCoeffs T (Arithmetic.mulCoords T.levels.toList (coeffs a) (coeffs b))

instance {T : NumberTower} : Mul (Elem T) := ⟨mul⟩

/-- Recursive extended-gcd inversion, totalized by `0⁻¹ = 0`. -/
@[expose]
def inv {T : NumberTower} (a : Elem T) : Elem T :=
  ofCoeffs T (Arithmetic.invCoords T.levels.toList (coeffs a))

instance {T : NumberTower} : Inv (Elem T) := ⟨inv⟩

/-- Tower division. -/
@[expose]
def div {T : NumberTower} (a b : Elem T) : Elem T :=
  a * b⁻¹

instance {T : NumberTower} : Div (Elem T) := ⟨div⟩

/-- Rational scalar multiplication acts on every mixed-radix coordinate. -/
@[expose]
def smul {T : NumberTower} (q : Rat) (a : Elem T) : Elem T :=
  ofCoeffs T ((coeffs a).map fun c => q * c)

instance {T : NumberTower} : SMul Rat (Elem T) := ⟨smul⟩

/-- Dense univariate polynomials over a fixed tower. -/
abbrev Poly (T : NumberTower) := DensePoly (Elem T)

/-! Compiled rational-tower arithmetic checks. -/

#guard
    let a := ofRat rat 7
    let b := ofRat rat 3
    coeffs (a + b) = #[10] && coeffs (a - b) = #[4] &&
      coeffs (a * b) = #[21] && coeffs (a / b) = #[7 / 3] &&
      coeffs (0⁻¹ : Elem rat) = #[0]

end Hex.NumberTower
