/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexMatrix.Lists
public import HexSmith.Smith

public section

/-! List certificates for integer Smith normal form. -/

namespace Hex.Matrix

/-- Rank, diagonal and unimodular transforms of a Smith certificate. -/
structure SmithWitness where
  /-- Number of positive invariant factors. -/
  rank : Nat
  /-- The positive factors, in divisibility order. -/
  diag : List Int
  /-- The left unimodular transform. -/
  left : List (List Int)
  /-- An integer right inverse of the left transform. -/
  leftInv : List (List Int)
  /-- The right unimodular transform. -/
  right : List (List Int)
  /-- An integer right inverse of the right transform. -/
  rightInv : List (List Int)
  /-- The supplied product of the left transform with the input. -/
  intermediate : List (List Int)
  deriving Repr, Inhabited, DecidableEq

/-- Check all dimensions before the four product identities and Smith shape.
No elimination or packed matrix access occurs in this check. -/
@[expose] def checkSmithList (n m : Nat) (rows : List (List Int))
    (c : SmithWitness) : Bool :=
  Lists.shape n m rows &&
  Nat.ble c.rank n && Nat.ble c.rank m && Nat.beq c.diag.length c.rank &&
  Lists.shape n n c.left && Lists.shape n n c.leftInv &&
  Lists.shape m m c.right && Lists.shape m m c.rightInv &&
  Lists.shape n m c.intermediate &&
  Lists.all (fun i => decide (0 < Lists.entry 0 c.diag i)) c.rank &&
  Lists.all (fun i => decide
    (Lists.entry 0 c.diag (i + 1) % Lists.entry 0 c.diag i = 0)) (c.rank - 1) &&
  Lists.product n m c.left rows (Lists.get c.intermediate) &&
  Lists.product n m c.intermediate c.right (Lists.diagonal c.diag) &&
  Lists.product n n c.left c.leftInv Lists.identity &&
  Lists.product m m c.right c.rightInv Lists.identity

/-- Produce a list certificate from one Smith reduction. -/
def smithWitness (A : Matrix Int n m) : SmithWitness :=
  let s := snfData A
  let rows {k l : Nat} (B : Matrix Int k l) := B.rows.toList.map (·.toList)
  { rank := s.rank
    diag := s.diag.toList
    left := rows s.left
    leftInv := rows s.leftInv
    right := rows s.right
    rightInv := rows s.rightInv
    intermediate := rows (s.left * A) }

end Hex.Matrix
