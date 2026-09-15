/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKronecker.Size

@[expose] public section

namespace Hex.Kronecker

abbrev TermMatrix := List (List (Hex.MvPoly.Kernel.PolyList Int))

def matrixShape (k n m : Nat) (a : TermMatrix) : Bool :=
  a.length == n && a.all (fun row => row.length == m && row.all (termShape k))

def matrixBounds (cap k : Nat) (a : TermMatrix) : List (List Bounds) :=
  a.map (fun row => row.map (termBounds cap k))

/-- Transpose bounds; shape validation precedes this operation. -/
def boundColumns (k : Nat) : Nat → List (List Bounds) → List (List Bounds)
  | 0, _ => []
  | m + 1, rows =>
      rows.map (fun row => row.headD (Bounds.zero k)) ::
        boundColumns k m (rows.map List.tail)

/-- A dot-product bound adds degrees before taking componentwise maxima. -/
def dotBounds (cap k : Nat) : List Bounds → List Bounds → Bounds
  | a :: as, b :: bs => (a.mul cap b).add cap (dotBounds cap k as bs)
  | _, _ => Bounds.zero k

/-- Collect the polynomial dot products in one row. -/
def rowBounds (cap k : Nat) (row : List Bounds) : List (List Bounds) → List Bounds
  | [] => []
  | col :: cols => dotBounds cap k row col :: rowBounds cap k row cols

def productBounds (cap k : Nat) (cols : List (List Bounds)) :
    List (List Bounds) → List (List Bounds)
  | [] => []
  | row :: rows => rowBounds cap k row cols :: productBounds cap k cols rows

/-- The common degree box and coefficient bound across output comparisons. -/
def commonBounds (cap k : Nat) : List Bounds → List Bounds → Bounds
  | a :: as, b :: bs => (a.add cap b).sup (commonBounds cap k as bs)
  | _, _ => Bounds.zero k

/-- Include the operands and full convolution products of the outer packing. -/
def SizeBound.withMode (s : SizeBound) (budget : Budget) (mode : MulMode) (r : Nat) :
    SizeBound :=
  match mode with
  | .plain => s
  | .signedPacked =>
      let slotBits := if r == 0 then 0 else r.log2 + 2 * (s.innerBits - 1) + 1
      let resultBits := 2 * r * slotBits + 2
      { s with outerSlotBits? := some slotBits
               packedBits := min (max s.innerBits resultBits) (budget.maxPackedBits + 1)
               limitingStage := if s.innerBits < resultBits then .result else .inner }

/-- Preflight for a rectangular integer polynomial matrix product. -/
def sizeMulTerms (budget : Budget) (mode : MulMode) (k n r m : Nat)
    (a b c : TermMatrix) : Except SizeError SizeBound :=
  if !(matrixShape k n r a && matrixShape k r m b && matrixShape k n m c) then
    .error .matrixShape
  else
    let cap := 2 ^ budget.maxPackedBits
    let ab := matrixBounds cap k a
    let bb := matrixBounds cap k b
    let cb := matrixBounds cap k c
    let products := productBounds cap k (boundColumns k m bb) ab
    let common := commonBounds cap k products.flatten cb.flatten
    let observed := ab.flatten ++ bb.flatten ++ cb.flatten ++ products.flatten
    .ok ((makeSize budget common observed).withMode budget mode r)

def differenceBounds (cap : Nat) : List Bounds → List Bounds → List Bounds
  | a :: as, b :: bs => a.add cap b :: differenceBounds cap as bs
  | _, _ => []

/-- Preflight for one integer quotient witness per output entry. -/
def sizeMulTermsMod (budget : Budget) (mode : MulMode) (k n r m p : Nat)
    (a b c q : TermMatrix) : Except SizeError SizeBound :=
  if p == 0 then .error .modulus
  else if !(matrixShape k n r a && matrixShape k r m b &&
      matrixShape k n m c && matrixShape k n m q) then .error .matrixShape
  else if !(a.all (fun row => row.all (termResidues p)) &&
      b.all (fun row => row.all (termResidues p)) &&
      c.all (fun row => row.all (termResidues p))) then .error .residue
  else if !(q.all (fun row => row.all (Hex.MvPoly.Kernel.isCanonical k))) then
    .error .quotient
  else
    let cap := 2 ^ budget.maxPackedBits
    let ab := matrixBounds cap k a
    let bb := matrixBounds cap k b
    let cb := matrixBounds cap k c
    let qb := matrixBounds cap k q
    let products := productBounds cap k (boundColumns k m bb) ab
    let differences := differenceBounds cap products.flatten cb.flatten
    let scaled := qb.flatten.map ((Bounds.mk (zeroDegrees k) (min p cap)).mul cap)
    let common := commonBounds cap k differences scaled
    let observed := ab.flatten ++ bb.flatten ++ cb.flatten ++ qb.flatten ++
      products.flatten ++ differences ++ scaled
    .ok ((makeSize budget common observed).withMode budget mode r)

end Hex.Kronecker
