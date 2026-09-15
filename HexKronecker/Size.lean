/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKronecker.Expr

@[expose] public section

namespace Hex.Kronecker

/-- Structural degree and coefficient bounds for one polynomial value. -/
structure Bounds where
  degrees : List Nat
  height : Nat
  deriving Repr

namespace Bounds

def zero (k : Nat) : Bounds := ⟨zeroDegrees k, 0⟩

def add (cap : Nat) (a b : Bounds) : Bounds :=
  ⟨maxDegrees a.degrees b.degrees, Saturating.add cap a.height b.height⟩

def mul (cap : Nat) (a b : Bounds) : Bounds :=
  ⟨addDegrees a.degrees b.degrees, Saturating.mul cap a.height b.height⟩

def pow (cap : Nat) (a : Bounds) (n : Nat) : Bounds :=
  ⟨scaleDegrees n a.degrees, Saturating.pow cap a.height n⟩

/-- The largest bounds among several independent outputs. -/
def sup (a b : Bounds) : Bounds :=
  ⟨maxDegrees a.degrees b.degrees, max a.height b.height⟩

end Bounds

/-- Analyze each subtree once, accumulating its bounds without list append. -/
def Expr.analyze (cap k : Nat) : Expr → List Bounds → Bounds × List Bounds
  | .int z, acc =>
      let b := Bounds.mk (zeroDegrees k) (min z.natAbs cap)
      (b, b :: acc)
  | .atom i, acc =>
      let b := Bounds.mk (atomDegrees k i) (min 1 cap)
      (b, b :: acc)
  | .add a b, acc | .sub a b, acc =>
      let (a, acc) := a.analyze cap k acc
      let (b, acc) := b.analyze cap k acc
      let c := a.add cap b
      (c, c :: acc)
  | .mul a b, acc =>
      let (a, acc) := a.analyze cap k acc
      let (b, acc) := b.analyze cap k acc
      let c := a.mul cap b
      (c, c :: acc)
  | .neg a, acc =>
      let (a, acc) := a.analyze cap k acc
      (a, a :: acc)
  | .pow a n, acc =>
      let (a, acc) := a.analyze cap k acc
      let c := a.pow cap n
      (c, c :: acc)

/-- Bounds for the supplied support, including zero-coefficient terms. -/
def termBounds (cap k : Nat) : Hex.MvPoly.Kernel.PolyList Int → Bounds
  | [] => Bounds.zero k
  | (e, c) :: ts => (Bounds.mk e (min c.natAbs cap)).add cap (termBounds cap k ts)

/-- Validate every exponent-list length. -/
def termShape (k : Nat) : Hex.MvPoly.Kernel.PolyList Int → Bool
  | [] => true
  | (e, _) :: ts => e.length == k && termShape k ts

/-- Canonical residue representatives; quotient coefficients remain integers. -/
def termResidues (p : Nat) : Hex.MvPoly.Kernel.PolyList Int → Bool
  | [] => true
  | (_, c) :: ts => (0 ≤ c && c < (p : Int)) && termResidues p ts

/-- Exact mixed-radix strides. These are exponents, not the packed powers. -/
def makeStrides (s : Nat) : List Nat → List Nat
  | [] => []
  | d :: ds => s :: makeStrides (s * (d + 1)) ds

/-- Dense digit count, saturated at the digit limit plus one. -/
def denseDigits (cap : Nat) : List Nat → Nat
  | [] => min 1 cap
  | d :: ds => Saturating.mul cap (d + 1) (denseDigits cap ds)

/-- Signed bit bound before saturation. -/
def Bounds.bits (strides : List Nat) (width : Nat) (b : Bounds) : Nat :=
  code strides b.degrees * width + b.height.log2 + 2

/-- Maximum over every operand and subtree, including operands multiplied by zero. -/
def maxBits (strides : List Nat) (width : Nat) : List Bounds → Nat
  | [] => 0
  | b :: bs => max (b.bits strides width) (maxBits strides width bs)

/-- The ordinary dot product is the default; signed packing is separately budgeted. -/
inductive MulMode where
  | plain
  | signedPacked
  deriving Repr, BEq, Inhabited

/-- The operation giving the maximum packed-size bound. -/
inductive Stage where
  | inner
  | outerRow
  | outerColumn
  | result
  deriving Repr, BEq, Inhabited

/-- Preflight metadata. Values at a saturation threshold are lower bounds;
all fields of accepted reports are exact structural bounds. -/
structure SizeBound where
  degrees : List Nat
  strides : List Nat
  digits : Nat
  coefficientBound : Nat
  digitBits : Nat
  outerSlotBits? : Option Nat := none
  packedBits : Nat
  limitingStage : Stage := .inner
  /-- Signed bit bound for inner values, before the optional outer packing. -/
  innerBits : Nat
  deriving Repr

def SizeBound.accepts (s : SizeBound) (budget : Budget) : Bool :=
  s.digits ≤ budget.maxDenseDigits && s.packedBits ≤ budget.maxPackedBits

/-- Errors distinguish malformed inputs from valid inputs exceeding a budget. -/
inductive SizeError where
  | atomIndex
  | termShape
  | matrixShape
  | modulus
  | residue
  | quotient
  deriving Repr, BEq

/-- Construct an inner plan without evaluating any packed value. -/
def makeSize (budget : Budget) (common : Bounds) (observed : List Bounds) : SizeBound :=
  let strides := makeStrides 1 common.degrees
  let width := common.height.log2 + 2
  let bits := min (maxBits strides width observed) (budget.maxPackedBits + 1)
  { degrees := common.degrees, strides := strides
    digits := denseDigits (budget.maxDenseDigits + 1) common.degrees
    coefficientBound := common.height, digitBits := width
    packedBits := bits, innerBits := bits }

/-- Plan for equality of two unnormalized expression trees. -/
def sizeExprEq (budget : Budget) (k : Nat) (lhs rhs : Expr) : Except SizeError SizeBound :=
  if !(lhs.wellFormed k && rhs.wellFormed k) then .error .atomIndex else
    let cap := 2 ^ budget.maxPackedBits
    let (l, bs) := lhs.analyze cap k []
    let (r, bs) := rhs.analyze cap k bs
    .ok (makeSize budget (l.add cap r) bs)

/-- Plan for two integer term lists. -/
def sizeTermsEq (budget : Budget) (k : Nat) (lhs rhs : Hex.MvPoly.Kernel.PolyList Int) :
    Except SizeError SizeBound :=
  if !(termShape k lhs && termShape k rhs) then .error .termShape else
    let cap := 2 ^ budget.maxPackedBits
    let l := termBounds cap k lhs
    let r := termBounds cap k rhs
    .ok (makeSize budget (l.add cap r) [l, r])

/-- Plan for the comparison `lhs - rhs = p * Q`, including the subtraction. -/
def sizeExprEqMod (budget : Budget) (k p : Nat) (lhs rhs : Expr)
    (q : Hex.MvPoly.Kernel.PolyList Int) : Except SizeError SizeBound :=
  if p == 0 then .error .modulus
  else if !(lhs.wellFormed k && rhs.wellFormed k) then .error .atomIndex
  else if !(lhs.residues p && rhs.residues p) then .error .residue
  else if !(Hex.MvPoly.Kernel.isCanonical k q) then .error .quotient
  else
    let cap := 2 ^ budget.maxPackedBits
    let (l, bs) := lhs.analyze cap k []
    let (r, bs) := rhs.analyze cap k bs
    let quotient := termBounds cap k q
    let scaled := (Bounds.mk (zeroDegrees k) (min p cap)).mul cap quotient
    let difference := l.add cap r
    .ok (makeSize budget (difference.add cap scaled) (difference :: scaled :: quotient :: bs))

/-- The term-list quotient-witness plan. -/
def sizeTermsEqMod (budget : Budget) (k p : Nat)
    (lhs rhs q : Hex.MvPoly.Kernel.PolyList Int) : Except SizeError SizeBound :=
  if p == 0 then .error .modulus
  else if !(termShape k lhs && termShape k rhs) then .error .termShape
  else if !(termResidues p lhs && termResidues p rhs) then .error .residue
  else if !(Hex.MvPoly.Kernel.isCanonical k q) then .error .quotient
  else
    let cap := 2 ^ budget.maxPackedBits
    let l := termBounds cap k lhs
    let r := termBounds cap k rhs
    let quotient := termBounds cap k q
    let scaled := (Bounds.mk (zeroDegrees k) (min p cap)).mul cap quotient
    let difference := l.add cap r
    .ok (makeSize budget (difference.add cap scaled) [l, r, quotient, scaled, difference])

end Hex.Kronecker
