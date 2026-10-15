/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexMatrix.Lists

public section

/-! Certificates and structural arithmetic for exact positive definiteness. -/

namespace Hex.PosDef

/-- An integer with an imaginary integer component. -/
structure Gaussian where
  /-- Real component. -/
  re : Int
  /-- Imaginary component. -/
  im : Int
  deriving Repr, Inhabited, DecidableEq, BEq

namespace Gaussian

@[expose] protected def zero : Gaussian := ⟨0, 0⟩
@[expose] protected def one : Gaussian := ⟨1, 0⟩
@[expose] protected def add (a b : Gaussian) : Gaussian :=
  ⟨Int.add a.re b.re, Int.add a.im b.im⟩
@[expose] protected def neg (a : Gaussian) : Gaussian := ⟨Int.neg a.re, Int.neg a.im⟩
@[expose] protected def mul (a b : Gaussian) : Gaussian :=
  ⟨Int.sub (Int.mul a.re b.re) (Int.mul a.im b.im),
    Int.add (Int.mul a.re b.im) (Int.mul a.im b.re)⟩
@[expose] def conj (a : Gaussian) : Gaussian := ⟨a.re, Int.neg a.im⟩

instance : Zero Gaussian := ⟨Gaussian.zero⟩
instance : One Gaussian := ⟨Gaussian.one⟩
instance : Add Gaussian := ⟨Gaussian.add⟩
instance : Neg Gaussian := ⟨Gaussian.neg⟩
instance : Mul Gaussian := ⟨Gaussian.mul⟩
instance : Sub Gaussian := ⟨fun a b => a + -b⟩

/-- Component equality, exposed for kernel reduction. -/
@[expose] def eq (a b : Gaussian) : Bool :=
  decide (a.re = b.re) && decide (a.im = b.im)

end Gaussian

/-- A congruence transform, or an integer positive vector. -/
inductive PositiveCert (R : Type) where
  /-- Leading entries of each row of a lower triangular congruence transform. -/
  | triangular (transform : List (List R))
  /-- A strictly positive integer vector with strictly positive matrix product. -/
  | positiveVector (vec : List Int)
  deriving Repr, Inhabited, DecidableEq

/-- A coordinate mismatch, or a nonzero vector with nonpositive quadratic value. -/
inductive NegativeCert (R : Type) where
  /-- Coordinates witnessing failure of Hermitian symmetry. -/
  | notHermitian (i j : Nat)
  /-- A nonzero vector whose quadratic value is real and nonpositive. -/
  | nonpositive (vec : List R)
  deriving Repr, Inhabited, DecidableEq

/-- A classification retains its polarity. -/
inductive Certificate (R : Type) where
  /-- Evidence for positive definiteness. -/
  | positive (cert : PositiveCert R)
  /-- Evidence against positive definiteness. -/
  | negative (cert : NegativeCert R)
  deriving Repr, Inhabited, DecidableEq

/-- The positive-vector specialization is explicitly selected. -/
inductive Method where
  /-- The general no-swap fraction-free method. -/
  | triangular
  /-- The explicitly selected real positive-vector specialization. -/
  | positiveVector
  deriving Repr, Inhabited, DecidableEq

/-- Capability declines and producer failures carry no mathematical assertion. -/
inductive Error where
  /-- The selected specialization cannot supply a certificate. -/
  | unsupported (reason : String)
  /-- The producer encountered an invariant or certificate-validation failure. -/
  | rejected
  deriving Repr, Inhabited, DecidableEq

namespace Lists

open Hex.Matrix.Lists (entry all)

/-- Arithmetic operations shared by the two concrete list checkers. -/
structure Arithmetic (R : Type) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  conj : R → R
  eq : R → R → Bool
  positive : R → Bool
  nonpositive : R → Bool

@[expose] def intArithmetic : Arithmetic Int :=
  ⟨0, 1, Int.add, Int.mul, id, fun a b => decide (a = b),
    fun a => decide (0 < a), fun a => decide (a ≤ 0)⟩

@[expose] def gaussianArithmetic : Arithmetic Gaussian :=
  ⟨Gaussian.zero, Gaussian.one, Gaussian.add, Gaussian.mul, Gaussian.conj, Gaussian.eq,
    fun a => decide (a.im = 0) && decide (0 < a.re),
    fun a => decide (a.im = 0) && decide (a.re ≤ 0)⟩

@[expose] def shape (n m : Nat) (rows : List (List R)) : Bool :=
  Nat.beq rows.length n && rows.all (fun row => Nat.beq row.length m)

@[expose] def triangularShape : Nat → List (List R) → Bool
  | _, [] => true
  | k, row :: rows => Nat.beq row.length (k + 1) && triangularShape (k + 1) rows

@[expose] def get (a : Arithmetic R) (rows : List (List R)) (i j : Nat) : R :=
  entry a.zero (entry [] rows i) j

@[expose] def column (a : Arithmetic R) (j : Nat) : List (List R) → List R
  | [] => []
  | row :: rows => entry a.zero row j :: column a j rows

/-- Transpose once, padding short rows with the arithmetic zero. -/
@[expose] def columns (a : Arithmetic R) : Nat → List (List R) → List (List R)
  | 0, _ => []
  | m + 1, rows => rows.map (List.headD · a.zero) :: columns a m (rows.map List.tail)

/-- Compare corresponding list entries by structural recursion. -/
@[expose] def paired (p : R → R → Bool) : List R → List R → Bool
  | [], [] => true
  | x :: xs, y :: ys => p x y && paired p xs ys
  | _, _ => false

/-- Visit each entry together with its index, without indexed list reads. -/
@[expose] def indexedAll (p : Nat → S → Bool) (xs : List S) : Bool :=
  xs.zipIdx.all fun (x,i) => p i x

@[expose] def dot (a : Arithmetic R) : List R → List R → R
  | x :: xs, y :: ys => a.add (a.mul x y) (dot a xs ys)
  | _, _ => a.zero

@[expose] def mulVec (a : Arithmetic R) (rows : List (List R)) (v : List R) : List R :=
  rows.map (fun row => dot a row v)

/-- Compare rows against their already materialized conjugate columns. -/
@[expose] def conjugateEq (a : Arithmetic R) (rows cols : List (List R)) : Bool :=
  (rows.zip cols).all fun (row, col) => paired (fun x y => a.eq x (a.conj y)) row col

@[expose] def hermitian (a : Arithmetic R) (n : Nat) (rows : List (List R)) : Bool :=
  conjugateEq a rows (columns a n rows)

@[expose] def triangular (a : Arithmetic R) (n : Nat)
    (rows transform : List (List R)) : Bool :=
  let cols := columns a n rows
  Nat.beq transform.length n && triangularShape 0 transform && conjugateEq a rows cols &&
    all (fun i =>
      let t := entry [] transform i
      all (fun j => a.eq (dot a t (entry [] cols j)) a.zero) i &&
      a.positive (a.mul (dot a t (entry [] cols i)) (a.conj (entry a.zero t i)))) n

@[expose] def negative (a : Arithmetic R) (n : Nat) (rows : List (List R)) :
    NegativeCert R → Bool
  | .notHermitian i j => Nat.blt i n && Nat.blt j n &&
      !(a.eq (get a rows i j) (a.conj (get a rows j i)))
  | .nonpositive v => Nat.beq v.length n && v.any (fun x => !(a.eq x a.zero)) &&
      a.nonpositive (dot a (v.map a.conj) (mulVec a rows v))

end Lists

namespace Int

open Hex.Matrix.Lists (all entry)
open Lists (intArithmetic)

/-- The independent positive-vector conditions, including exact shape. -/
@[expose] def checkVector (n : Nat) (rows : List (List Int)) (v : List Int) : Bool :=
  Nat.beq v.length n && Lists.hermitian intArithmetic n rows &&
    Lists.indexedAll (fun i row => Lists.indexedAll (fun j x => Nat.beq i j || decide (x ≤ 0)) row) rows &&
    v.all (fun x => decide (0 < x)) &&
    (Lists.mulVec intArithmetic rows v).all (fun x => decide (0 < x))

/-- Check a positive certificate without elimination or rational arithmetic. -/
@[expose] def checkPositive (n : Nat) (rows : List (List Int)) (c : PositiveCert Int) : Bool :=
  Lists.shape n n rows && match c with
    | .triangular t => Lists.triangular intArithmetic n rows t
    | .positiveVector v => checkVector n rows v

/-- Check a refutation independently of the producer. -/
@[expose] def checkNegative (n : Nat) (rows : List (List Int)) (c : NegativeCert Int) : Bool :=
  Lists.shape n n rows && Lists.negative intArithmetic n rows c

end Int

namespace Gaussian

/-- Gaussian certificates use the congruence method. -/
@[expose] def checkPositive (n : Nat) (rows : List (List Gaussian))
    (c : PositiveCert Gaussian) : Bool :=
  Lists.shape n n rows && match c with
    | .triangular t => Lists.triangular Lists.gaussianArithmetic n rows t
    | .positiveVector _ => false

/-- Check both Gaussian negative-certificate constructors. -/
@[expose] def checkNegative (n : Nat) (rows : List (List Gaussian))
    (c : NegativeCert Gaussian) : Bool :=
  Lists.shape n n rows && Lists.negative Lists.gaussianArithmetic n rows c

end Gaussian

end Hex.PosDef
