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

private theorem add_assoc (a b c : List Int) : add (add a b) c = add a (add b c) := by
  induction a generalizing b c with
  | nil => simp [add]
  | cons a as ih =>
    cases b with
    | nil => simp [add]
    | cons b bs =>
      cases c with
      | nil => simp [add]
      | cons c cs => simp [add, ih, Int.add_assoc]

-- Rows are read-only. Borrow their spines so each dot avoids reference-count
-- writes along both rows; the polynomial accumulator remains owned.
private def dotAcc (a b : @& List (List Int)) (acc : List Int) : List Int :=
  match a, b with
  | a :: as, b :: bs => dotAcc as bs (add acc (mul a b))
  | _, _ => acc

private theorem dotAcc_eq (a b : List (List Int)) (acc : List Int) :
    dotAcc a b acc = add acc (dot a b) := by
  induction a generalizing b acc with
  | nil => cases acc <;> simp [dotAcc, dot, add]
  | cons a as ih =>
    cases b with
    | nil => cases acc <;> simp [dotAcc, dot, add]
    | cons b bs => simp [dotAcc, dot, ih, add_assoc]

/-- Native dot product with a tail-recursive accumulator. -/
def dotImpl (a b : @& List (List Int)) : List Int := dotAcc a b []

@[csimp] theorem dot_eq_impl : @dot = @dotImpl := by
  funext a b
  simp [dotImpl, dotAcc_eq, add]

private def dotArrayAcc (a b : @& Array (List Int)) : Nat → Nat → List Int → List Int
  | 0, _, acc => acc
  | fuel + 1, i, acc =>
    dotArrayAcc a b fuel (i + 1) (add acc (mul (a[i]?.getD []) (b[i]?.getD [])))

/-- Native dot product over compact rows, truncated at the shorter row. -/
def dotArray (a b : @& Array (List Int)) : List Int :=
  dotArrayAcc a b (min a.size b.size) 0 []

private theorem dotArrayAcc_eq (a b : Array (List Int)) (fuel i : Nat) (acc : List Int) :
    dotArrayAcc a b fuel i acc =
      ((List.range' i fuel).map fun j => mul (a[j]?.getD []) (b[j]?.getD [])).foldl add acc := by
  induction fuel generalizing i acc with
  | zero => simp [dotArrayAcc]
  | succ fuel ih => simp [dotArrayAcc, List.range'_succ, ih]

private theorem products_eq (a b : List (List Int)) :
    ((List.range (min a.length b.length)).map fun i =>
      mul (a[i]?.getD []) (b[i]?.getD [])) = List.zipWith mul a b := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have ha : i < a.length := by simpa using (Nat.lt_of_lt_of_le (by simpa using hi) (Nat.min_le_left _ _))
    have hb : i < b.length := by simpa using (Nat.lt_of_lt_of_le (by simpa using hi) (Nat.min_le_right _ _))
    simp [ha, hb]

private theorem fold_products (a b : List (List Int)) (acc : List Int) :
    (List.zipWith mul a b).foldl add acc = add acc (dot a b) := by
  induction a generalizing b acc with
  | nil => cases acc <;> simp [dot, add]
  | cons a as ih =>
    cases b with
    | nil => cases acc <;> simp [dot, add]
    | cons b bs => simp [dot, ih, add_assoc]

theorem dotArray_toArray (a b : List (List Int)) :
    dotArray a.toArray b.toArray = dot a b := by
  simp only [dotArray, dotArrayAcc_eq, List.size_toArray, List.getElem?_toArray,
    ← List.range_eq_range']
  rw [products_eq, fold_products]
  simp [add]

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

private def checkDotArray (M : Nat) (f v : List Int)
    (a b : @& Array (List Int)) (q : List Int) : Bool :=
  eqMod M (dotArray a b) (add v (mul f q))

private def zeroDotsArray (M : Nat) (f : List Int) (a : Array (List Int)) :
    List (Array (List Int)) → List (List Int) → Bool
  | [], [] => true
  | b :: bs, q :: qs => checkDotArray M f [] a b q && zeroDotsArray M f a bs qs
  | _, _ => false

private theorem zeroDots_toArray (M : Nat) (f : List Int) (a : List (List Int))
    (bs : List (List (List Int))) (qs : List (List Int)) :
    zeroDotsArray M f a.toArray (bs.map List.toArray) qs = zeroDots M f a bs qs := by
  induction bs generalizing qs with
  | nil => cases qs <;> simp [zeroDotsArray, zeroDots]
  | cons b bs ih =>
    cases qs <;> simp [zeroDotsArray, zeroDots, checkDotArray, checkDot, dotArray_toArray, ih]

private def lowerArray (M : Nat) (f : List Int) :
    List (Array (List Int)) → List (Array (List Int)) → List (List (List Int)) → Bool
  | [], [], [] => true
  | a :: as, b :: bs, (q :: qs) :: rest =>
      checkDotArray M f [1] a b q && zeroDotsArray M f a bs qs && lowerArray M f as bs rest
  | _, _, _ => false

private theorem lowerArray_toArray (M : Nat) (f : List Int)
    (A B Q : List (List (List Int))) :
    lowerArray M f (A.map List.toArray) (B.map List.toArray) Q = lowerCheck M f A B Q := by
  induction A generalizing B Q with
  | nil => cases B <;> cases Q <;> simp [lowerArray, lowerCheck]
  | cons a as ih =>
    cases B with
    | nil => cases Q <;> simp [lowerArray, lowerCheck]
    | cons b bs =>
      cases Q with
      | nil => simp [lowerArray, lowerCheck]
      | cons q qs =>
        cases q <;> simp [lowerArray, lowerCheck, checkDotArray, checkDot,
          dotArray_toArray, zeroDots_toArray, ih]

/-- Compact both sets of rows once, before their repeated native dot products.
Conversion is part of checking, not certificate preparation. The reference
list checker remains the definition used by the kernel. -/
def lowerCheckImpl (M : Nat) (f : List Int) (A B Q : List (List (List Int))) : Bool :=
  lowerArray M f (A.map List.toArray) (B.map List.toArray) Q

@[csimp] theorem lowerCheck_eq_impl : @lowerCheck = @lowerCheckImpl := by
  funext M f A B Q
  exact (lowerArray_toArray M f A B Q).symm

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
