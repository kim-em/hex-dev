/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLLL.Lattice
public import HexMatrix.Certificate

@[expose] public section

namespace Hex.LatticeEnum

/-- An independent integer row basis, including rectangular and empty bases. -/
structure Basis (n m : Nat) where
  /-- Rows in the original input coordinates. -/
  rows : Matrix Int n m
  /-- Positivity of the executable leading Gram determinants. -/
  independent : Matrix.independent rows

/-- Check independence without changing the input row lattice. -/
def ofMatrix? (rows : Matrix Int n m) : Option (Basis n m) :=
  if h : Matrix.independent rows then some ⟨rows, h⟩ else none

/-- Reconstruct an ambient integer vector from original-basis coefficients. -/
def vector (b : Basis n m) (z : Vector Int n) : Vector Int m :=
  Matrix.vecMul z b.rows

/-- Squared Euclidean distance to a rational target. -/
def distance (v : Vector Int m) (t : Vector Rat m) : Rat :=
  ((v.map fun x : Int => (x : Rat)) - t).normSq

/-- Squared distance of an original-basis coefficient vector to the target. -/
def distanceSq (b : Basis n m) (t : Vector Rat m) (z : Vector Int n) : Rat :=
  distance (vector b z) t

/-- A reported point retains its original coefficients and exact distance. -/
structure Point (n m : Nat) where
  /-- Coefficients in the original input basis. -/
  coefficients : Vector Int n
  /-- Ambient integer coordinates. -/
  ambient : Vector Int m
  /-- Exact squared distance to the query target. -/
  distanceSq : Rat
  deriving DecidableEq, Repr

/-- Construct a point by direct reconstruction and distance evaluation. -/
def point (b : Basis n m) (t : Vector Rat m) (z : Vector Int n) : Point n m :=
  ⟨z, vector b z, distanceSq b t z⟩

/-- Replay a point's coefficient and distance claims. -/
def checkPoint (b : Basis n m) (t : Vector Rat m) (p : Point n m) : Bool :=
  decide (p = point b t p.coefficients)

/-- Deterministic public order on points, by ambient integer coordinates. -/
def pointLE (p q : Point n m) : Bool :=
  decide (compare p.ambient.toList q.ambient.toList ≠ .gt)

/-- Sort a complete result independently of traversal order. -/
def sortPoints (ps : List (Point n m)) : List (Point n m) :=
  ps.mergeSort pointLE

/-- Every reconstructed vector lies in the original integer row lattice. -/
theorem vector_mem (b : Basis n m) (z : Vector Int n) :
    b.rows.memLattice (vector b z) := ⟨z, rfl⟩

/-- Directly constructed points pass their replay check. -/
theorem checkPoint_point (b : Basis n m) (t : Vector Rat m) (z : Vector Int n) :
    checkPoint b t (point b t z) = true := by
  simp [checkPoint, point]

end Hex.LatticeEnum
