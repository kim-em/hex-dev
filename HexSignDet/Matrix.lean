/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRank.Cert
public import HexMatrix.MatrixAlgebra

public section

/-! Integer moment systems for sign determination. Scaled left inverses are
checked in the declared row/column order, independently of rank certificates. -/
namespace Hex.SignDet

open scoped Hex

/-- A moment entry. Shape and exponent guards belong to the system checker. -/
@[expose] def entry (e : List Nat) (s : List Int) : Int :=
  ((e.zip s).map fun (k, v) => v ^ k).foldr (· * ·) 1

/-- Build the integer moment matrix in the literal orders supplied. -/
@[expose] def momentMatrix {r c : Nat} (rows : Vector (List Nat) r)
    (cols : Vector (List Int) c) : Matrix Int r c :=
  Matrix.ofFn fun i j => entry rows[i] cols[j]

/-- A square moment system with integer counts and a scaled left inverse. -/
structure System (r : Nat) where
  rows : Vector (List Nat) r
  columns : Vector (List Int) r
  counts : Vector Int r
  values : Vector Int r
  inverse : Matrix Int r r
  denominator : Int

/-- Check every dimension-dependent literal before using the moment equations.
Counts are kept as integers; no rounding, truncation or clamping occurs. -/
@[expose] def System.check {r : Nat} (arity : Nat) (s : System r) : Bool :=
  s.rows.toList.all (fun e => decide (e.length = arity) && e.all (· ≤ 2)) &&
  s.columns.toList.all (fun c => decide (c.length = arity) &&
    c.all (fun x => decide (x = -1 ∨ x = 0 ∨ x = 1))) &&
  decide s.columns.toList.Nodup &&
  s.counts.toList.all (· ≥ 0) &&
  decide (s.denominator ≠ 0) &&
  (let m := momentMatrix s.rows s.columns
   decide (s.inverse * m = Matrix.scale s.denominator (Matrix.identity r)) &&
   decide (m * s.counts = s.values))

/-- Accepted systems retain both literal integer identities. -/
theorem System.identities {r : Nat} {arity : Nat} {s : System r}
    (h : s.check arity = true) :
    s.denominator ≠ 0 ∧
    s.inverse * momentMatrix s.rows s.columns =
      Matrix.scale s.denominator (Matrix.identity r) ∧
    momentMatrix s.rows s.columns * s.counts = s.values := by
  simp only [System.check, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2.1, h.2.2⟩

private theorem scale_identity_vec {r : Nat} (d : Int) (v : Vector Int r) :
    Matrix.scale d (Matrix.identity r) * v = d • v := by
  apply Vector.ext
  intro i hi
  let ii : Fin r := ⟨i, hi⟩
  change (Matrix.scale d (Matrix.identity r) * v)[ii] = (d • v)[ii]
  rw [Matrix.scale_eq_smul, Matrix.getElem_mulVec, Matrix.row_smul,
    Vector.dotProduct_smul_left]
  have h := congrArg (fun w : Vector Int r => w[ii]) (Matrix.identity_mulVec v)
  rw [Matrix.getElem_mulVec] at h
  rw [h]
  exact (Vector.getElem_smul d v i hi).symm

/-- The checked counts are the unique integer solution. This is finite linear
algebra only: coverage of realizable sign conditions is a separate obligation. -/
theorem System.unique {r : Nat} {arity : Nat} {s : System r}
    (h : s.check arity = true) (v : Vector Int r)
    (hv : momentMatrix s.rows s.columns * v = s.values) : v = s.counts := by
  obtain ⟨hd, hi, hc⟩ := s.identities h
  have hm : momentMatrix s.rows s.columns * v =
      momentMatrix s.rows s.columns * s.counts := hv.trans hc.symm
  have he := congrArg (fun w : Vector Int r => s.inverse * w) hm
  rw [← Matrix.mul_assoc_vec, ← Matrix.mul_assoc_vec, hi,
    scale_identity_vec, scale_identity_vec] at he
  apply Vector.ext
  intro i hir
  have hx := congrArg (fun w : Vector Int r => w[i]) he
  simp only [Vector.getElem_smul] at hx
  change s.denominator * v[i] = s.denominator * s.counts[i] at hx
  exact Int.eq_of_mul_eq_mul_left hd hx

end Hex.SignDet
