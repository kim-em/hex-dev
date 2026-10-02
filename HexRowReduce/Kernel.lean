/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexMatrix.Scaled

public section

/-! Structural integer certificates for field inversion and complete solving. -/

namespace Hex.Matrix

open Lists

namespace FieldLists

/-- A positive scale and an exact rectangular block. -/
@[expose] def matrix (n m : Nat) (a : ScaledRows) : Bool :=
  Nat.blt 0 a.denom && shape n m a.nums

/-- A positive scale and an exact vector length. -/
@[expose] def vector (n : Nat) (a : Scaled) : Bool :=
  Nat.blt 0 a.denom && Nat.beq a.nums.length n

/-- Matrix multiplication with denominators cleared once per identity. -/
@[expose] def product (n m : Nat) (a b c : ScaledRows) : Bool :=
  all (fun i => all (fun j => decide
    (Int.mul (dot (entry [] a.nums i) (column j b.nums)) (Int.ofNat c.denom) =
      Int.mul (get c.nums i j) (Int.ofNat (Nat.mul a.denom b.denom)))) m) n

/-- Inverse products need only the scaled identity, without materializing it. -/
@[expose] def inverse (n : Nat) (a b : ScaledRows) : Bool :=
  Lists.product n n a.nums b.nums
    (fun i j => Int.mul (Int.ofNat (Nat.mul a.denom b.denom)) (identity i j))

/-- A vector represented as a single-column block. -/
@[expose] def columnBlock (a : Scaled) : ScaledRows :=
  ⟨a.denom, a.nums.map (fun z => [z])⟩

/-- A vector represented as a single-row block. -/
@[expose] def rowBlock (a : Scaled) : ScaledRows := ⟨a.denom, [a.nums]⟩

/-- Zero right product. -/
@[expose] def kernel (n : Nat) (a : ScaledRows) (v : Scaled) : Bool :=
  all (fun i => decide (dot (entry [] a.nums i) v.nums = 0)) n

/-- Zero left product and nonzero pairing with the right-hand side. -/
@[expose] def separator (m : Nat) (a : ScaledRows) (b y : Scaled) : Bool :=
  all (fun j => decide (dot y.nums (column j a.nums) = 0)) m &&
    decide (dot y.nums b.nums ≠ 0)

/-- Structural common denominator, without GCD or well-founded recursion. -/
@[expose] def denominator (qs : List Rat) : Nat :=
  qs.foldl (fun d q => if Nat.beq (Nat.mod d q.den) 0 then d else Nat.mul d q.den) 1

/-- A direct residual check chooses its scale by a structural list fold. -/
@[expose] def encode (qs : List Rat) : Scaled :=
  let d := denominator qs
  ⟨d, qs.map (fun q => Int.mul q.num (Int.ofNat (Nat.div d q.den)))⟩

/-- Encode a matrix with the same structural scale fold as a direct residual check. -/
@[expose] def encodeRows (rows : List (List Rat)) : ScaledRows :=
  let d := denominator rows.flatten
  ⟨d, rows.map (fun row => row.map (fun q =>
    Int.mul q.num (Int.ofNat (Nat.div d q.den))))⟩

end FieldLists

/-- An arbitrary inverse or nonzero right-kernel witness. -/
inductive InverseWitness where
  | invertible (input value : ScaledRows)
  | singular (input : ScaledRows) (kernel : Scaled) (index : Nat)
  deriving Repr, Inhabited, DecidableEq

/-- Check either mathematical outcome independently of row reduction. -/
@[expose] def checkInverseList (n : Nat) (rows : List (List Rat))
    (c : InverseWitness) : Bool :=
  match c with
  | .invertible a b =>
    FieldLists.matrix n n a && scaleRows a.denom rows a.nums &&
    FieldLists.matrix n n b && FieldLists.inverse n a b && FieldLists.inverse n b a
  | .singular a v k =>
    FieldLists.matrix n n a && scaleRows a.denom rows a.nums &&
    FieldLists.vector n v && Nat.blt k n && decide (entry 0 v.nums k ≠ 0) &&
    FieldLists.kernel n a v

/-- The list data needed to reconstruct a complete reduced-row-echelon witness. -/
structure SolveBasis where
  reduced : ScaledRows
  transform : ScaledRows
  inverse : ScaledRows
  rank : Nat
  pivots : List Nat
  free : List Nat
  value : Scaled
  nullity : Nat
  basis : ScaledRows
  deriving Repr, Inhabited, DecidableEq

/-- Complete affine data or a separating row. -/
inductive SolveWitness where
  | consistent (input : ScaledRows) (rhs : Scaled) (data : SolveBasis)
  | inconsistent (input : ScaledRows) (rhs separator : Scaled)
  deriving Repr, Inhabited, DecidableEq

namespace FieldLists

/-- A sorted in-range pivot list and the full reduced-row-echelon clauses. -/
@[expose] def echelon (n m : Nat) (d : SolveBasis) : Bool :=
  Nat.ble d.rank n && Nat.ble d.rank m && Nat.beq d.pivots.length d.rank &&
  all (fun i => Nat.blt (entry m d.pivots i) m &&
    all (fun j => decide (entry m d.pivots j < entry m d.pivots i)) i &&
    all (fun j => decide (get d.reduced.nums j (entry m d.pivots i) =
      if Nat.beq i j then Int.ofNat d.reduced.denom else 0)) n &&
    all (fun j => decide (get d.reduced.nums i j = 0)) (entry m d.pivots i)) d.rank &&
  all (fun i => Nat.blt i d.rank ||
    all (fun j => decide (get d.reduced.nums i j = 0)) m) n

/-- Free columns in increasing order, canonical particular solution and basis. -/
@[expose] def freeData (m : Nat) (d : SolveBasis) : Bool :=
  decide (d.free = (List.range m).filter (fun j => !d.pivots.contains j)) &&
  Nat.beq d.nullity (m - d.rank) && Nat.beq d.free.length d.nullity &&
  all (fun k => decide (entry 0 d.value.nums (entry m d.free k) = 0) &&
    all (fun l => decide (get d.basis.nums (entry m d.free l) k =
      if Nat.beq k l then Int.ofNat d.basis.denom else 0)) d.nullity &&
    all (fun i => decide
      (Int.mul (get d.basis.nums (entry m d.pivots i) k) (Int.ofNat d.reduced.denom) =
        Int.neg (Int.mul (get d.reduced.nums i (entry m d.free k))
          (Int.ofNat d.basis.denom)))) d.rank) d.nullity

end FieldLists

/-- Validate the entire affine space or the inconsistency witness. -/
@[expose] def checkSolveList (n m : Nat) (rows : List (List Rat)) (rhs : List Rat)
    (c : SolveWitness) : Bool :=
  match c with
  | .consistent a b d =>
    FieldLists.matrix n m a && scaleRows a.denom rows a.nums &&
    FieldLists.vector n b && scaleRow b.denom rhs b.nums &&
    FieldLists.matrix n m d.reduced && FieldLists.matrix n n d.transform &&
    FieldLists.matrix n n d.inverse && FieldLists.vector m d.value &&
    FieldLists.matrix m d.nullity d.basis &&
    FieldLists.product n m d.transform a d.reduced &&
    FieldLists.inverse n d.transform d.inverse && FieldLists.echelon n m d &&
    FieldLists.product n 1 a (FieldLists.columnBlock d.value) (FieldLists.columnBlock b) &&
    FieldLists.freeData m d
  | .inconsistent a b y =>
    FieldLists.matrix n m a && scaleRows a.denom rows a.nums &&
    FieldLists.vector n b && scaleRow b.denom rhs b.nums &&
    FieldLists.vector n y && FieldLists.separator m a b y

/-- Check any supplied solution, with no canonical-solution restriction. -/
@[expose] def checkSolutionList (n m : Nat) (rows : List (List Rat))
    (rhs candidate : List Rat) : Bool :=
  let a := FieldLists.encodeRows rows
  let b := FieldLists.encode rhs
  let x := FieldLists.encode candidate
  FieldLists.matrix n m a && scaleRows a.denom rows a.nums &&
  FieldLists.vector n b && scaleRow b.denom rhs b.nums &&
  FieldLists.vector m x && scaleRow x.denom candidate x.nums &&
  FieldLists.product n 1 a (FieldLists.columnBlock x) (FieldLists.columnBlock b)

end Hex.Matrix
