/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTower.Data
public meta import HexNumberFieldTower.Data

public section

/-!
# Runtime-indexed mixed-radix tower arithmetic

These operations consume raw top-first level lists. Certified public tower
arithmetic is a thin dependent wrapper defined later.
-/
namespace Hex.NumberTower.Arithmetic

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

/-- A block of fixed-width coordinate addition is the sum of the blocks. -/
theorem block_add (count width index : Nat) (a b : Array Rat)
    (hindex : index < count) :
    block (addCoords (count * width) a b) index width =
      addCoords width (block a index width) (block b index width) := by
  apply Array.ext
  · simp [block, addCoords]
  · intro i hi₁ hi₂
    have hi : i < width := by
      simpa [addCoords] using hi₂
    have hglobal : index * width + i < count * width := by
      calc
        index * width + i < index * width + width :=
          Nat.add_lt_add_left hi _
        _ = (index + 1) * width := by simp [Nat.add_mul]
        _ ≤ count * width :=
          Nat.mul_le_mul_right width (Nat.succ_le_of_lt hindex)
    simp [block, addCoords, Array.getD, hglobal]

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
level; defensive nonconstant/zero gcd branches are unreachable for certified
level lists. -/
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

/-! Compiled raw arithmetic regressions. -/

private def sqrtTwoLevel : Level where
  degree := 2
  defining := #[#[-2], #[0]]
  root := AlgebraicNumber.zero.toRoot

private def sqrtThreeLevel : Level where
  degree := 2
  defining := #[#[-3, 0], #[0, 0]]
  root := AlgebraicNumber.zero.toRoot

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

end Hex.NumberTower.Arithmetic
