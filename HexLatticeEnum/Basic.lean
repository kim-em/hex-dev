/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexLLL.Lattice
public import HexMatrix.Certificate
public import HexBasic.Sort

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

/-- Input checking succeeds exactly for independent rows. -/
@[simp] theorem ofMatrix?_isSome (rows : Matrix Int n m) :
    (ofMatrix? rows).isSome = decide rows.independent := by
  unfold ofMatrix?
  split <;> simp_all

/-- An accepted basis retains exactly the supplied matrix. -/
@[simp] theorem ofMatrix?_eq_some (rows : Matrix Int n m) (b : Basis n m) :
    ofMatrix? rows = some b ↔ b.rows = rows := by
  constructor
  · intro h
    unfold ofMatrix? at h
    split at h
    · cases Option.some.inj h
      rfl
    · cases h
  · intro h
    subst rows
    cases b
    simp [ofMatrix?, *]

/-- Reconstruct an ambient integer vector from original-basis coefficients. -/
def vector (b : Basis n m) (z : Vector Int n) : Vector Int m :=
  Matrix.vecMul z b.rows

/-- Kernel-reducible rational coordinate cast. -/
def castVector (v : Vector Int m) : Vector Rat m :=
  Hex.Vector.ofFn' fun i => (v[i] : Rat)

/-- Kernel-reducible coordinate subtraction. -/
def subtract (u v : Vector Rat m) : Vector Rat m :=
  Hex.Vector.ofFn' fun i => u[i] - v[i]

/-- Coordinate casting agrees with the standard vector map. -/
@[simp] theorem castVector_eq (v : Vector Int m) :
    castVector v = v.map (fun x : Int => (x : Rat)) := by
  apply Vector.ext
  intro i hi
  simp [castVector]

/-- Coordinate subtraction agrees with vector subtraction. -/
@[simp] theorem subtract_eq (u v : Vector Rat m) : subtract u v = u - v := by
  apply Vector.ext
  intro i hi
  simp [subtract]

/-- Squared Euclidean distance to a rational target. -/
def distance (v : Vector Int m) (t : Vector Rat m) : Rat :=
  (subtract (castVector v) t).normSq

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

/-- Reconstruct a point from raw rows, requiring no independence proof for replay. -/
def pointRows (rows : Matrix Int n m) (t : Vector Rat m) (z : Vector Int n) : Point n m :=
  let v := Matrix.vecMul z rows
  ⟨z, v, distance v t⟩

/-- Construct a point by direct reconstruction and distance evaluation. -/
def point (b : Basis n m) (t : Vector Rat m) (z : Vector Int n) : Point n m :=
  pointRows b.rows t z

/-- Replay a point's coefficient and distance claims. -/
def checkPoint (rows : Matrix Int n m) (t : Vector Rat m) (p : Point n m) : Bool :=
  decide (p = pointRows rows t p.coefficients)

/-- Deterministic public order on points, by ambient integer coordinates. -/
def pointLE (p q : Point n m) : Bool :=
  decide (compare p.ambient.toList q.ambient.toList ≠ .gt)

/-- Sort a complete result independently of traversal order. -/
def sortPoints (ps : List (Point n m)) : List (Point n m) :=
  Hex.List.sort ps pointLE

/-- Every reconstructed vector lies in the original integer row lattice. -/
theorem vector_mem (b : Basis n m) (z : Vector Int n) :
    b.rows.memLattice (vector b z) := ⟨z, rfl⟩

/-- Directly constructed points pass their replay check. -/
theorem checkPoint_point (b : Basis n m) (t : Vector Rat m) (z : Vector Int n) :
    checkPoint b.rows t (point b t z) = true := by
  simp [checkPoint, point, pointRows]

end Hex.LatticeEnum
