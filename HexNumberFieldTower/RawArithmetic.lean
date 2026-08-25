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

/-- A fold whose steps preserve array size leaves the size unchanged. -/
private theorem foldl_array_size {α β : Type} (indices : List β)
    (step : Array α → β → Array α) (initial : Array α)
    (hstep : ∀ work index, (step work index).size = work.size) :
    (indices.foldl step initial).size = initial.size := by
  induction indices generalizing initial with
  | nil => rfl
  | cons index indices ih =>
      simp only [List.foldl_cons]
      rw [ih, hstep]

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

/-- Adding back the subtrahend recovers the fixed-width minuend. -/
theorem add_subCoords (n : Nat) (a b : Array Rat) :
    addCoords n (subCoords n a b) b = fixedCoeffs n a := by
  apply Array.ext
  · simp [addCoords, subCoords, fixedCoeffs]
  · intro i hi₁ hi₂
    simp [addCoords, subCoords, fixedCoeffs, Array.getD,
      Rat.sub_add_cancel]

/-- One mixed-radix block. -/
@[expose]
def block (a : Array Rat) (index width : Nat) : Array Rat :=
  (Vector.ofFn fun i : Fin width => a.getD (index * width + i.val) 0).toArray

/-- A block of fixed-width coordinates is the fixed-width source block. -/
theorem block_fixed (count width index : Nat) (a : Array Rat)
    (hindex : index < count) :
    block (fixedCoeffs (count * width) a) index width =
      fixedCoeffs width (block a index width) := by
  apply Array.ext
  · simp [block, fixedCoeffs]
  · intro i hi₁ hi₂
    have hi : i < width := by
      simpa [fixedCoeffs] using hi₂
    have hglobal : index * width + i < count * width := by
      calc
        index * width + i < index * width + width :=
          Nat.add_lt_add_left hi _
        _ = (index + 1) * width := by simp [Nat.add_mul]
        _ ≤ count * width :=
          Nat.mul_le_mul_right width (Nat.succ_le_of_lt hindex)
    simp [block, fixedCoeffs, Array.getD, hglobal]

/-- The only nonzero block of the fixed-width coordinate one is its constant
block. -/
theorem block_one (count width index : Nat) (hindex : index < count) :
    block (fixedCoeffs (count * width) #[1]) index width =
      if index = 0 then fixedCoeffs width #[1]
      else fixedCoeffs width #[] := by
  by_cases hindex0 : index = 0
  · subst index
    apply Array.ext
    · simp [block, fixedCoeffs]
    · intro i hi₁ hi₂
      have hi : i < width := by
        simpa [fixedCoeffs] using hi₂
      have htotal : 0 < count * width :=
        Nat.mul_pos hindex (Nat.zero_lt_of_lt hi)
      rcases i with _ | i
      · simp [block, fixedCoeffs, Array.getD, Nat.ne_of_gt htotal]
      · simp [block, fixedCoeffs, Array.getD]
  · simp only [if_neg hindex0]
    apply Array.ext
    · simp [block, fixedCoeffs]
    · intro i hi₁ hi₂
      have hi : i < width := by
        simpa [fixedCoeffs] using hi₂
      have hwidth : 0 < width := Nat.zero_lt_of_lt hi
      have hmul : 0 < index * width :=
        Nat.mul_pos (Nat.pos_of_ne_zero hindex0) hwidth
      simp [block, fixedCoeffs, Array.getD, Nat.ne_of_gt hmul]

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

/-- Flattening fixed-width blocks always produces the requested total width. -/
@[simp]
theorem flattenBlocks_size (count width : Nat) (blocks : Array (Array Rat)) :
    (flattenBlocks count width blocks).size = count * width := by
  by_cases hwidth : width = 0
  · simp [flattenBlocks, hwidth]
  · simp [flattenBlocks, hwidth]

/-- Reading an in-range block after flattening recovers that source block at
the fixed lower width. -/
theorem block_flatten (count width index : Nat)
    (blocks : Array (Array Rat)) (hindex : index < count) :
    block (flattenBlocks count width blocks) index width =
      fixedCoeffs width (blocks.getD index #[]) := by
  by_cases hwidth : width = 0
  · subst width
    simp [block, flattenBlocks, fixedCoeffs]
  · apply Array.ext
    · simp [block, fixedCoeffs]
    · intro i hi₁ hi₂
      have hi : i < width := by
        simpa [fixedCoeffs] using hi₂
      have hglobal : index * width + i < count * width := by
        calc
          index * width + i < index * width + width :=
            Nat.add_lt_add_left hi _
          _ = (index + 1) * width := by simp [Nat.add_mul]
          _ ≤ count * width :=
            Nat.mul_le_mul_right width (Nat.succ_le_of_lt hindex)
      have hdiv : (index * width + i) / width = index := by
        calc
          _ = (width * index + i) / width := by
            rw [Nat.mul_comm index width]
          _ = index + i / width :=
            Nat.mul_add_div (Nat.pos_of_ne_zero hwidth) index i
          _ = index := by simp [Nat.div_eq_of_lt hi]
      have himod : i % width = i := Nat.mod_eq_of_lt hi
      simp [block, flattenBlocks, fixedCoeffs, Array.getD, hwidth, hglobal,
        hdiv, himod]

/-- Add one row of schoolbook block products to a convolution workspace. -/
@[expose]
def convolveRow (degree width i : Nat)
    (multiply : Array Rat → Array Rat → Array Rat)
    (a b : Array Rat) (work : Array (Array Rat)) : Array (Array Rat) :=
  let zeroBlock : Array Rat := Array.replicate width 0
  (List.range degree).foldl
    (fun work j =>
      let product := multiply (block a i width) (block b j width)
      let k := i + j
      work.set! k (addCoords width (work.getD k zeroBlock) product))
    work

/-- One convolution row edits the work array in place, preserving its
size. -/
@[simp]
theorem convolveRow_size (degree width i : Nat)
    (multiply : Array Rat → Array Rat → Array Rat)
    (a b : Array Rat) (work : Array (Array Rat)) :
    (convolveRow degree width i multiply a b work).size = work.size := by
  unfold convolveRow
  apply foldl_array_size
  intro inner j
  simp

/-- Schoolbook convolution of fixed-width coefficient blocks. -/
@[expose]
def convolve (degree width : Nat)
    (multiply : Array Rat → Array Rat → Array Rat)
    (a b : Array Rat) : Array (Array Rat) :=
  let zeroBlock : Array Rat := Array.replicate width 0
  let work := Array.replicate (2 * degree - 1) zeroBlock
  (List.range degree).foldl
    (fun work i => convolveRow degree width i multiply a b work)
    work

/-- Convolution allocates exactly the coefficient range of a product of two
polynomials of degree below `degree`. -/
@[simp]
theorem convolve_size (degree width : Nat)
    (multiply : Array Rat → Array Rat → Array Rat)
    (a b : Array Rat) :
    (convolve degree width multiply a b).size = 2 * degree - 1 := by
  unfold convolve
  rw [foldl_array_size]
  · simp
  · intro work i
    simp

/-- Apply all lower-coefficient corrections for eliminating the coefficient
at `k` with a monic relation. -/
@[expose]
def reduceCoeffs (degree width k : Nat) (defining : Array (Array Rat))
    (multiply : Array Rat → Array Rat → Array Rat)
    (work : Array (Array Rat)) : Array (Array Rat) :=
  let zeroBlock : Array Rat := Array.replicate width 0
  let high := work.getD k zeroBlock
  (List.range degree).foldl
    (fun work j =>
      let relation := defining.getD j zeroBlock
      let correction := multiply high relation
      let target := k - degree + j
      work.set! target
        (subCoords width (work.getD target zeroBlock) correction))
    work

/-- One coefficient-reduction step edits the work array in place, preserving
its size. -/
@[simp]
theorem reduceCoeffs_size (degree width k : Nat)
    (defining : Array (Array Rat))
    (multiply : Array Rat → Array Rat → Array Rat)
    (work : Array (Array Rat)) :
    (reduceCoeffs degree width k defining multiply work).size = work.size := by
  unfold reduceCoeffs
  apply foldl_array_size
  intro inner j
  simp

/-- Eliminate the coefficient at `k`, then discard it. -/
@[expose]
def reduceAt (degree width k : Nat) (defining : Array (Array Rat))
    (multiply : Array Rat → Array Rat → Array Rat)
    (work : Array (Array Rat)) : Array (Array Rat) :=
  (reduceCoeffs degree width k defining multiply work).take k

/-- One descending reduction step removes exactly its top coefficient. -/
@[simp]
theorem reduceAt_size (degree width k : Nat)
    (defining : Array (Array Rat))
    (multiply : Array Rat → Array Rat → Array Rat)
    (work : Array (Array Rat)) (hsize : work.size = k + 1) :
    (reduceAt degree width k defining multiply work).size = k := by
  simp [reduceAt, hsize]

/-- Descending monic reduction of all coefficients at or above `degree`. -/
@[expose]
def reduce (degree width : Nat) (defining : Array (Array Rat))
    (multiply : Array Rat → Array Rat → Array Rat) :
    Nat → Array (Array Rat) → Array (Array Rat)
  | 0, work => work.take degree
  | fuel + 1, work =>
      reduce degree width defining multiply fuel
        (reduceAt degree width (degree + fuel) defining multiply work)

/-- Descending reduction consumes its whole high-coefficient fuel. -/
@[simp]
theorem reduce_size (degree width fuel : Nat)
    (defining : Array (Array Rat))
    (multiply : Array Rat → Array Rat → Array Rat)
    (work : Array (Array Rat)) (hsize : work.size = degree + fuel) :
    (reduce degree width defining multiply fuel work).size = degree := by
  induction fuel generalizing work with
  | zero => simp [reduce, hsize]
  | succ fuel ih =>
      have hstep :
          (reduceAt degree width (degree + fuel) defining multiply work).size =
            degree + fuel := by
        apply reduceAt_size
        omega
      simpa [reduce] using
        ih (reduceAt degree width (degree + fuel) defining multiply work) hstep

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
        let convolved := convolve d lowerDim (mulCoords lower) a b
        let reduced := reduce d lowerDim level.defining (mulCoords lower)
          (d - 1) convolved
        flattenBlocks d lowerDim reduced

/-- Recursive multiplication returns exactly one mixed-radix coordinate
vector. -/
@[simp]
theorem mulCoords_size (levels : List Level) (a b : Array Rat) :
    (mulCoords levels a b).size = levelsDim levels := by
  induction levels generalizing a b with
  | nil => simp [mulCoords, levelsDim]
  | cons level lower ih =>
      by_cases hdegree : level.degree = 0
      · simp [mulCoords, levelsDim, hdegree]
      · simp [mulCoords, levelsDim, hdegree]

/-- Dynamically indexed tower coefficient used internally when an algorithm
recurses through runtime level data rather than a dependent `NumberTower`.
The `raw` helper normalizes to the represented mixed-radix dimension. -/
structure RawElem (levels : List Level) where
  data : Array Rat

/-- Wrap coordinate data as a `RawElem`, zero-padding or truncating to the
represented mixed-radix dimension. -/
@[expose]
def raw (levels : List Level) (data : Array Rat) : RawElem levels :=
  .mk (fixedCoeffs (levelsDim levels) data)

/-! `RawElem` operations delegate to the runtime-indexed coordinate
functions above; `Inv` and `Div` follow after `invCoords`. -/

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

/-- Canonical lower-tower coefficient used by recursive inversion. Unlike the
general-purpose `RawElem`, this type carries the fixed-width invariant needed
by the semantic field bridge for polynomial xgcd. -/
structure Coeff (levels : List Level) where
  data : Array Rat
  size_eq : data.size = levelsDim levels

/-- Normalize arbitrary data into a canonical lower-tower coefficient. -/
@[expose]
def Coeff.ofData (levels : List Level) (data : Array Rat) : Coeff levels :=
  ⟨fixedCoeffs (levelsDim levels) data, by simp [fixedCoeffs]⟩

/-! `Coeff` operations delegate to the same coordinate functions, carrying
the fixed-width invariant through each result. -/

instance (levels : List Level) : DecidableEq (Coeff levels) :=
  fun a b =>
    match decEq a.data.toList b.data.toList with
    | isTrue h => isTrue (by cases a; cases b; simpa using h)
    | isFalse h => isFalse fun hab => h (by simp [hab])

instance (levels : List Level) : Zero (Coeff levels) :=
  ⟨Coeff.ofData levels #[]⟩

instance (levels : List Level) : One (Coeff levels) :=
  ⟨Coeff.ofData levels #[1]⟩

instance (levels : List Level) : Add (Coeff levels) :=
  ⟨fun a b =>
    ⟨addCoords (levelsDim levels) a.data b.data, by simp [addCoords]⟩⟩

instance (levels : List Level) : Sub (Coeff levels) :=
  ⟨fun a b =>
    ⟨subCoords (levelsDim levels) a.data b.data, by simp [subCoords]⟩⟩

instance (levels : List Level) : Neg (Coeff levels) :=
  ⟨fun a => ⟨negCoords (levelsDim levels) a.data, by simp [negCoords]⟩⟩

instance (levels : List Level) : Mul (Coeff levels) :=
  ⟨fun a b =>
    ⟨mulCoords levels a.data b.data, mulCoords_size levels a.data b.data⟩⟩

/-- View one top-level coordinate array as a polynomial over canonical lower
tower coefficients. -/
@[expose]
def Coeff.value (level : Level) (lower : List Level) (a : Array Rat) :
    DensePoly (Coeff lower) :=
  DensePoly.ofCoeffs <| ((List.range level.degree).map fun i =>
    Coeff.ofData lower (block a i (levelsDim lower))).toArray

/-- The monic defining relation as a polynomial over canonical lower-tower
coefficients. -/
@[expose]
def Coeff.relation (level : Level) (lower : List Level) :
    DensePoly (Coeff lower) :=
  DensePoly.ofCoeffs <| ((List.range level.degree).map fun i =>
    Coeff.ofData lower (level.defining.getD i #[])).toArray.push 1

/-- Recursive inverse coordinates. The zero convention is inherited at every
level; defensive nonconstant/zero gcd branches are unreachable for certified
level lists. -/
@[expose]
def invCoords : (levels : List Level) → Array Rat → Array Rat
  | [], a => #[if a.getD 0 0 = 0 then 0 else (a.getD 0 0)⁻¹]
  | level :: lower, a =>
      let lowerDim := levelsDim lower
      let d := level.degree
      if (fixedCoeffs (d * lowerDim) a).all (fun q => q = 0) then
        Array.replicate (d * lowerDim) 0
      else
        letI : Inv (Coeff lower) :=
          ⟨fun x => Coeff.ofData lower (invCoords lower x.data)⟩
        letI : Div (Coeff lower) := ⟨fun x y => x * y⁻¹⟩
        let value := Coeff.value level lower a
        let defining := Coeff.relation level lower
        let result := DensePoly.xgcdLeft value defining
        if result.gcd.size = 1 then
          let c := result.gcd.leadingCoeff
          if c = 0 then
            Hex.panicWith (Array.replicate (d * lowerDim) 0)
              "NumberTower.inv: zero constant gcd"
          else
            let normalized := DensePoly.scale c⁻¹ result.left % defining
            flattenBlocks d lowerDim <| ((List.range d).map fun i =>
              (normalized.coeff i).data).toArray
        else
          Hex.panicWith (Array.replicate (d * lowerDim) 0)
            "NumberTower.inv: nonconstant gcd"

/-- Recursive inversion always returns the canonical mixed-radix width,
including its defensive zero fallbacks. -/
@[simp]
theorem invCoords_size (levels : List Level) (a : Array Rat) :
    (invCoords levels a).size = levelsDim levels := by
  induction levels generalizing a with
  | nil =>
      simp [invCoords, levelsDim]
  | cons level lower ih =>
      simp only [invCoords, levelsDim]
      split
      · simp
      · split
        · split <;> simp [Hex.panicWith]
        · simp [Hex.panicWith]

instance (levels : List Level) : Inv (RawElem levels) :=
  ⟨fun a => raw levels (invCoords levels a.data)⟩

instance (levels : List Level) : Div (RawElem levels) :=
  ⟨fun a b => a * b⁻¹⟩

instance (levels : List Level) : Inv (Coeff levels) :=
  ⟨fun a => Coeff.ofData levels (invCoords levels a.data)⟩

instance (levels : List Level) : Div (Coeff levels) :=
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
