/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexMatrix.Lists
public import HexHermite.Hermite

public section

/-! Structural list certificates for Hermite form and lattice remainders. -/

namespace Hex.Matrix

/-- Hermite form, pivot columns and inverse integer transforms. -/
structure HermiteWitness where
  rank : Nat
  pivots : List Nat
  form : List (List Int)
  transform : List (List Int)
  inverse : List (List Int)
  deriving Repr, Inhabited, DecidableEq

/-- Check the full HNF shape independently of the transform products. -/
@[expose] def HermiteWitness.checkForm (n m : Nat) (c : HermiteWitness) : Bool :=
  Nat.ble c.rank n && Nat.ble c.rank m &&
  Nat.beq c.pivots.length c.rank &&
  Lists.all (fun i => Nat.blt (Lists.entry 0 c.pivots i) m) c.rank &&
  Lists.all (fun i => Lists.all (fun j =>
    !(Nat.blt i j) || Nat.blt (Lists.entry 0 c.pivots i) (Lists.entry 0 c.pivots j))
      c.rank) c.rank &&
  Lists.all (fun i =>
    let p := Lists.entry 0 c.pivots i
    decide (0 < Lists.get c.form i p) &&
    Lists.all (fun j => !(Nat.blt j p) || decide (Lists.get c.form i j = 0)) m &&
    Lists.all (fun row =>
      (!(Nat.blt i row) || decide (Lists.get c.form row p = 0)) &&
      (!(Nat.blt row i) ||
        (decide (0 ≤ Lists.get c.form row p) &&
          decide (Lists.get c.form row p < Lists.get c.form i p)))) n) c.rank &&
  Lists.all (fun row => !(Nat.ble c.rank row) ||
    Lists.all (fun j => decide (Lists.get c.form row j = 0)) m) n

/-- Check all matrix dimensions, HNF clauses and the two transform products. -/
@[expose] def checkHermiteList (n m : Nat) (rows : List (List Int))
    (c : HermiteWitness) : Bool :=
  Lists.shape n m rows && Lists.shape n m c.form &&
  Lists.shape n n c.transform && Lists.shape n n c.inverse &&
  c.checkForm n m &&
  Lists.product n m c.transform rows (Lists.get c.form) &&
  Lists.product n n c.transform c.inverse Lists.identity

/-- Coefficients and a reduced residual for a lattice query. -/
structure HermiteRemainder where
  coeffs : List Int
  residual : List Int
  deriving Repr, Inhabited, DecidableEq

/-- Whether every residual coordinate vanishes. -/
@[expose] def HermiteRemainder.isZero (m : Nat) (r : HermiteRemainder) : Bool :=
  Lists.all (fun j => decide (Lists.entry 0 r.residual j = 0)) m

/-- Check the remainder identity and all pivot-coordinate bounds. -/
@[expose] def checkRemainder (m : Nat) (v : List Int)
    (c : HermiteWitness) (r : HermiteRemainder) : Bool :=
  Nat.beq v.length m && Nat.beq r.coeffs.length c.rank &&
  Nat.beq r.residual.length m &&
  Lists.all (fun j => decide (Lists.entry 0 v j =
    Int.add (Lists.dot r.coeffs (Lists.column j (c.form.take c.rank)))
      (Lists.entry 0 r.residual j))) m &&
  Lists.all (fun i =>
    let p := Lists.entry 0 c.pivots i
    decide (0 ≤ Lists.entry 0 r.residual p) &&
    decide (Lists.entry 0 r.residual p < Lists.get c.form i p)) c.rank

/-- Produce the list witness from one HNF reduction retaining its inverse. -/
def hermiteWitness (A : Matrix Int n m) : HermiteWitness :=
  let h := hnfWithInv A
  let rows {k l : Nat} (B : Matrix Int k l) := B.rows.toList.map (·.toList)
  { rank := h.rowData.rank
    pivots := h.rowData.pivotCols.toList.map (·.val)
    form := rows h.rowData.echelon
    transform := rows h.rowData.transform
    inverse := rows h.inverse }

/-- Forward HNF remainder calculation, used only by the compiled producer. -/
def hermiteRemainder (v : List Int) (c : HermiteWitness) : HermiteRemainder := Id.run do
  let mut residual := v.toArray
  let mut coeffs := #[]
  for i in [:c.rank] do
    let p := c.pivots[i]!
    let row := c.form[i]!.toArray
    let q := residual[p]! / row[p]!
    coeffs := coeffs.push q
    residual := residual.mapIdx fun j x => x - q * row[j]!
  return ⟨coeffs.toList, residual.toList⟩

end Hex.Matrix
