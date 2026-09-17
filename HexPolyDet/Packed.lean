/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyDet.Basic
public import HexKronecker.Check

@[expose] public section

namespace Hex.PolyDet

open Hex.Matrix Hex.Matrix.DetWitness Hex.MvPoly.Kernel

namespace Packed

/-- The leading square block used by a transform row. -/
def leading (r : Nat) (a : List (List R)) : List (List R) :=
  (a.take r).map (List.take r)

/-- The adjacent transform diagonal, or the final signed determinant. -/
def next (ops : DetOps R) (swaps : List (Nat × Nat)) (d : R)
    (i : Nat) (ts : List (List R)) : R :=
  match ts with
  | [] => ops.signed swaps d
  | t :: _ => ops.entry t (i + 1)

/-- Structural checks shared by the integer and residue packed checkers. -/
def rows (ops : DetOps R) (d : R) (swaps : List (Nat × Nat))
    (a : List (List R)) (product : Nat → List R → List (List R) → List R → Bool) :
    Nat → List (List R) → Bool
  | _, [] => true
  | i, t :: ts =>
      Nat.beq t.length (i + 1) && ops.validRow t &&
      !(ops.beq (ops.entry t i) ops.zero) &&
      product i t (leading (i + 1) a)
        (List.replicate i ops.zero ++ [next ops swaps d i ts]) &&
      rows ops d swaps a product (i + 1) ts

/-- Validate the unchanged determinant witness, substituting only its products. -/
def check (ops : DetOps R) (n : Nat) (a : List (List R))
    (product : Nat → List R → List (List R) → List R → Bool)
    (singular : List R → Bool) : DetWitness R → Bool
  | .triangular swaps ts d =>
      Nat.beq a.length n && rowLengths n a && ops.validRows a &&
      swapsOk n swaps && ops.valid d && Nat.beq ts.length n &&
      (if n == 0 then ops.beq d ops.one
       else ops.beq (ops.entry (row ts 0) 0) ops.one) &&
      rows ops d swaps (permute swaps a) product 0 ts
  | .singular v =>
      Nat.beq a.length n && rowLengths n a && ops.validRows a &&
      Nat.beq v.length n && ops.validRow v && ops.anyNonzero v && singular v

/-- Canonical residue representatives embedded coefficientwise in the integers. -/
def lift (a : PolyList Nat) : PolyList Int := a.map fun (e, c) => (e, (c : Int))

/-- One quotient row per triangular prefix, or one row for a singular witness. -/
def quotientShape (n : Nat) (w : DetWitness R)
    (qs : List (List (PolyList Int))) : Bool :=
  match w with
  | .triangular _ _ _ =>
      Nat.beq qs.length n && (qs.zipIdx).all (fun (q, i) => Nat.beq q.length (i + 1))
  | .singular _ => Nat.beq qs.length 1 && rowLengths n qs

end Packed

/-- Check the polynomial witness with bounded Kronecker row-prefix products. -/
def checkDetPolyPacked (budget : Kronecker.Budget) (mode : Kronecker.MulMode)
    (k n : Nat) (a : List (List (PolyList Int))) (w : DetWitness (PolyList Int)) : Bool :=
  Packed.check (ops k) n a
    (fun i t b c => Kronecker.checkMulTerms budget mode k 1 (i + 1) (i + 1) [t] b [c])
    (fun v => Kronecker.checkMulTerms budget mode k 1 n n [v] a [List.replicate n []]) w

/-- Residue products carry integer quotients; no packed integer is reduced modulo `p`. -/
def checkDetPolyPackedMod (budget : Kronecker.Budget) (mode : Kronecker.MulMode)
    (p k n : Nat) (a : List (List (PolyList Nat))) (w : DetWitness (PolyList Nat))
    (qs : List (List (PolyList Int))) : Bool :=
  !Nat.beq p 0 && Packed.quotientShape n w qs &&
  Packed.check (opsMod p k) n a
    (fun i t b c => Kronecker.checkMulTermsMod budget mode k 1 (i + 1) (i + 1) p
      [t.map Packed.lift] (b.map (List.map Packed.lift)) [c.map Packed.lift] [qs.getD i []])
    (fun v => Kronecker.checkMulTermsMod budget mode k 1 n n p
      [v.map Packed.lift] (a.map (List.map Packed.lift)) [List.replicate n []] qs) w

end Hex.PolyDet
