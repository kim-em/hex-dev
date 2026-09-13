/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRank.Kernel

public section

namespace Hex.Matrix

/-- Rank data over an integer polynomial quotient. Quotients certify the
polynomial relations; the kernel never performs polynomial division. -/
structure PolyWitness where
  /-- Certified rank. -/
  rank : Nat
  /-- Modulus for the lower bound. -/
  modulus : Nat
  /-- Inverse of the defining polynomial's leading coefficient modulo the modulus. -/
  leadingInv : Int
  /-- Selected rows. -/
  rows : List Nat
  /-- Selected columns. -/
  cols : List Nat
  /-- Columns of the modular transform, as polynomials. -/
  vt : List (List (List Int))
  /-- Division witnesses for the diagonal and upper triangle, row by row. -/
  lowerQuot : List (List (List Int))
  /-- Nonzero integer scaling the exact row relations. -/
  denom : Int
  /-- Coefficients expressing each nonpivot row in the pivot rows. -/
  z : List (List (List Int))
  /-- Division witnesses for the exact nonpivot row relations. -/
  upperQuot : List (List (List Int))
  deriving Repr, Inhabited, DecidableEq

namespace PolyWitness

/-- Coefficientwise addition, with implicit trailing zeros. -/
@[expose] def add : List Int → List Int → List Int
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => Int.add a b :: add as bs

/-- Multiply every coefficient by an integer. -/
@[expose] def scale (a : Int) : List Int → List Int
  | [] => []
  | b :: bs => Int.mul a b :: scale a bs

/-- Polynomial multiplication in ascending coefficient order. -/
@[expose] def mul : List Int → List Int → List Int
  | [], _ => []
  | a :: as, b => add (scale a b) (0 :: mul as b)

/-- All coefficients vanish modulo `M`. -/
@[expose] def zeroMod (M : Nat) : List Int → Bool
  | [] => true
  | a :: as => decide (Int.emod a (Int.ofNat M) = 0) && zeroMod M as

/-- Equality modulo `M`, allowing trailing zeros. Modulus zero checks exact
integer equality. Recursion is structural on the first list. -/
@[expose] def eqMod (M : Nat) : List Int → List Int → Bool
  | [], b => zeroMod M b
  | a :: as, [] => decide (Int.emod a (Int.ofNat M) = 0) && eqMod M as []
  | a :: as, b :: bs =>
      decide (Int.emod (Int.sub a b) (Int.ofNat M) = 0) && eqMod M as bs

/-- A dot product of polynomial lists, truncated at the shorter list. -/
@[expose] def dot : List (List Int) → List (List Int) → List Int
  | a :: as, b :: bs => add (mul a b) (dot as bs)
  | _, _ => []

/-- List access with a supplied zero value. -/
@[expose] def nth {α : Type} (zero : α) : List α → Nat → α
  | [], _ => zero
  | a :: _, 0 => a
  | _ :: as, i + 1 => nth zero as i

/-- Verify a dot product equals `v` in the polynomial quotient modulo `M`. -/
@[expose] def checkDot (M : Nat) (f v : List Int)
    (a b : List (List Int)) (q : List Int) : Bool :=
  eqMod M (dot a b) (add v (mul f q))

/-- Verify the strict upper triangle of one product row. -/
@[expose] def zeroDots (M : Nat) (f : List Int) (a : List (List Int)) :
    List (List (List Int)) → List (List Int) → Bool
  | [], [] => true
  | b :: bs, q :: qs => checkDot M f [] a b q && zeroDots M f a bs qs
  | _, _ => false

/-- Verify a lower unitriangular product in the modular quotient. -/
@[expose] def lowerCheck (M : Nat) (f : List Int) :
    List (List (List Int)) → List (List (List Int)) → List (List (List Int)) → Bool
  | [], [], [] => true
  | a :: as, b :: bs, (q :: qs) :: rest =>
      checkDot M f [1] a b q && zeroDots M f a bs qs && lowerCheck M f as bs rest
  | _, _, _ => false

/-- Verify one exact row relation using the transpose of the pivot rows. -/
@[expose] def rowCheck (f : List Int) (d : Int) (z : List (List Int)) :
    List (List Int) → List (List (List Int)) → List (List Int) → Bool
  | [], [], [] => true
  | a :: as, p :: ps, q :: qs =>
      eqMod 0 (scale d a) (add (dot z p) (mul f q)) && rowCheck f d z as ps qs
  | _, _, _ => false

/-- Verify the nonpivot rows, consuming one coefficient row and one quotient
row for each. -/
@[expose] def rowsCheck (f : List Int) (d : Int) (rows : List Nat)
    (pt : List (List (List Int))) : Nat → List (List (List Int)) →
    List (List (List Int)) → List (List (List Int)) → Bool
  | _, [], [], [] => true
  | i, a :: as, z, q =>
      if RankWitness.memNat i rows then rowsCheck f d rows pt (i + 1) as z q
      else match z, q with
        | z :: zs, q :: qs => rowCheck f d z a pt q && rowsCheck f d rows pt (i + 1) as zs qs
        | _, _ => false
  | _, _, _, _ => false

/-- Every row has the stated width. -/
@[expose] def rowsLen (m : Nat) : List (List (List Int)) → Bool
  | [] => true
  | a :: as => Nat.beq a.length m && rowsLen m as

/-- Select the minor as polynomial rows. -/
@[expose] def block (A : List (List (List Int))) (rows cols : List Nat) :
    List (List (List Int)) :=
  rows.map fun i => cols.map fun j => nth [] (nth [] A i) j

/-- Transpose the selected rows, preserving the ambient matrix width. -/
@[expose] def pivotCols (m : Nat) (A : List (List (List Int))) (rows : List Nat) :
    List (List (List Int)) :=
  (List.range m).map fun j => rows.map fun i => nth [] (nth [] A i) j

end PolyWitness

open PolyWitness in
/-- Check both rank bounds on integer polynomial data. `f` has its leading
coefficient last; its unit residue ensures the modular quotient is nontrivial. -/
@[expose] def checkRankPoly (n m : Nat) (f : List Int)
    (A : List (List (List Int))) (c : PolyWitness) : Bool :=
  Nat.beq A.length n && rowsLen m A && Nat.blt 1 c.modulus && Nat.blt 1 f.length &&
  eqMod c.modulus [Int.mul (f.getLastD 0) c.leadingInv] [1] &&
  Nat.beq c.rows.length c.rank && Nat.beq c.cols.length c.rank &&
  RankWitness.allLt n c.rows && RankWitness.allLt m c.cols && decide (c.denom ≠ 0) &&
  lowerCheck c.modulus f (block A c.rows c.cols) c.vt c.lowerQuot &&
  rowsCheck f c.denom c.rows (pivotCols m A c.rows) 0 A c.z c.upperQuot

end Hex.Matrix
