/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRankMathlib.Quotient
public import Mathlib.NumberTheory.Zsqrtd.Basic

public section

namespace HexMatrixMathlib.PolyWitness

open Hex.Matrix.PolyWitness

/-- The defining relation for integer quadratic pairs. -/
@[expose] def quadratic (d : Int) : List Int := [-d, 0, 1]

theorem eval_quadratic {R : Type*} [CommRing R] (x : R) (d : Int) :
    eval x (quadratic d) = -(d : R) + x * x := by simp [quadratic, eval]

/-- Certify rank over integer quadratic pairs, using the quotient by the same
quadratic relation modulo the certificate modulus. -/
theorem rank_eq_quadratic (d : Int) [IsDomain (Zsqrtd d)] (n m : Nat)
    (L : List (List (List Int))) (c : Hex.Matrix.PolyWitness)
    (h : Hex.Matrix.checkRankPoly n m (quadratic d) L c = true) :
    (ofPolys (Zsqrtd.sqrtd : Zsqrtd d) n m L).rank = c.rank := by
  have h' := h
  simp only [Hex.Matrix.checkRankPoly, Bool.and_eq_true, and_assoc] at h'
  obtain ⟨_, _, hM, hdeg, hu, _⟩ := h'
  have hM' : 1 < c.modulus := by simpa using hM
  have hdeg' : 1 < (quadratic d).length := by simpa using hdeg
  let f := quadratic d
  let S := ModQuot c.modulus f c.leadingInv
  let : Nontrivial S := modQuot_nontrivial c.modulus f c.leadingInv hM' hdeg' hu
  let root : S := AdjoinRoot.root (modPolynomial c.modulus f c.leadingInv)
  have hroot : root * root = (d : S) := by
    have hz := modRoot_eval c.modulus f c.leadingInv hu
    rw [eval_quadratic] at hz
    exact (neg_add_eq_zero.mp hz).symm
  let φ : Zsqrtd d →+* S := Zsqrtd.lift ⟨root, hroot⟩
  exact rank_eq_of_check φ Zsqrtd.sqrtd n m f L c
    (by rw [eval_quadratic, Zsqrtd.dmuld]; simp)
    (modQuot_char c.modulus f c.leadingInv) h

/-- The quadratic certificate for a matrix identified with its polynomial rows. -/
theorem rank_eq_quadratic' (d : Int) [IsDomain (Zsqrtd d)] {n m : Nat}
    (A : Matrix (Fin n) (Fin m) (Zsqrtd d)) (L : List (List (List Int)))
    (c : Hex.Matrix.PolyWitness) (hA : A = ofPolys Zsqrtd.sqrtd n m L)
    (h : Hex.Matrix.checkRankPoly n m (quadratic d) L c = true) : A.rank = c.rank :=
  hA ▸ rank_eq_quadratic d n m L c h

end HexMatrixMathlib.PolyWitness
