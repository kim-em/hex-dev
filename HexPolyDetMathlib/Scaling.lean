/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyDetMathlib.Sound

public section

namespace HexMatrixMathlib.DetPoly.Scaling

open scoped HexMvPolyMathlib
attribute [local instance 2000] Ring.toGrindRing

theorem add (a b p q : Rat) (s : Nat) (hp : p = s * a) (hq : q = s * b) :
    p + q = (s : Rat) * (a + b) := by
  rw [hp, hq]
  ring

theorem sub (a b p q : Rat) (s : Nat) (hp : p = s * a) (hq : q = s * b) :
    p - q = (s : Rat) * (a - b) := by
  rw [hp, hq]
  ring

theorem mul (a b p q : Rat) (s t : Nat) (hp : p = s * a) (hq : q = t * b) :
    p * q = ((s * t : Nat) : Rat) * (a * b) := by
  rw [hp, hq, Nat.cast_mul]
  ring

theorem neg (a p : Rat) (s : Nat) (hp : p = s * a) : -p = (s : Rat) * -a := by
  rw [hp]
  ring

theorem pow (a p : Rat) (s n : Nat) (hp : p = s * a) :
    p ^ n = ((s ^ n : Nat) : Rat) * a ^ n := by
  rw [hp, mul_pow, Nat.cast_pow]

theorem div (a b p : Rat) (s : Nat) (z : Int) (d : Nat)
    (hp : p = (s : Rat) * a) (hb : (z : Rat) = (d : Rat) / b) :
    (z : Rat) * p = ((s * d : Nat) : Rat) * (a / b) := by
  rw [hp, hb, Nat.cast_mul]
  simp only [div_eq_mul_inv]
  ring

theorem row (a p : Rat) (s t : Nat) (hp : p = (s : Rat) * a) :
    (t : Rat) * p = ((t * s : Nat) : Rat) * a := by
  rw [hp, Nat.cast_mul, mul_assoc]

/-- Cancel positive row and target scales from a cross-multiplied identity. -/
theorem cancel (s t : Nat) (a e : Rat) (hs : 0 < s) (ht : 0 < t)
    (h : (t : Rat) * ((s : Rat) * a) = (s : Rat) * ((t : Rat) * e)) : a = e := by
  have ht0 : (t : Rat) ≠ 0 := by exact_mod_cast ht.ne'
  have hs0 : (s : Rat) ≠ 0 := by exact_mod_cast hs.ne'
  apply mul_left_cancel₀ (mul_ne_zero ht0 hs0)
  simpa only [mul_assoc, mul_left_comm] using h

/-- Cancel the positive row and target scales after comparing the integer
polynomial lists by cross multiplication. -/
theorem target (k n : Nat)
    (w : Hex.Matrix.DetWitness (Hex.MvPoly.Kernel.PolyList Int))
    (ctx : Lean.RArray Rat) (A : Matrix (Fin n) (Fin n) Rat)
    (s : List Nat) (t : Nat) (q : Hex.MvPoly.Kernel.PolyList Int) (e : Rat)
    (hdet : (Hex.Matrix.DetWitness.prodNat s : Rat) * A.det =
      HexReflectMathlib.Kernel.hom k ctx
        (Hex.MvPoly.Kernel.denote (cmp := Hex.Mono.grevlex) (Polynomial.value w)))
    (ht : 0 < t) (hs : 0 < Hex.Matrix.DetWitness.prodNat s)
    (he : HexReflectMathlib.Kernel.hom k ctx
      (Hex.MvPoly.Kernel.denote (cmp := Hex.Mono.grevlex) q) = (t : Rat) * e)
    (hq : Hex.MvPoly.Kernel.beq
      (Hex.MvPoly.Kernel.smul (Int.ofNat t) (Polynomial.value w))
      (Hex.MvPoly.Kernel.smul (Int.ofNat (Hex.Matrix.DetWitness.prodNat s)) q) = true) :
    A.det = e := by
  have h := congrArg (fun p => HexReflectMathlib.Kernel.hom k ctx
    (Hex.MvPoly.Kernel.denote (cmp := Hex.Mono.grevlex) p))
      (Hex.MvPoly.Kernel.beq_eq_true_iff.mp hq)
  rw [HexReflectMathlib.Kernel.eval_smul, HexReflectMathlib.Kernel.eval_smul, he, ← hdet] at h
  apply cancel (Hex.Matrix.DetWitness.prodNat s) t A.det e hs ht
  simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using h


/-- Identification of the row-scaled symbolic literal. -/
theorem identify (n : Nat) (A B : Matrix (Fin n) (Fin n) Rat) (s : List Nat)
    (h : Polynomial.AllFin n (fun i => Polynomial.AllFin n
      (fun j => B i j = (s.getD i 1 : Rat) * A i j))) :
    B = Matrix.diagonal (fun i : Fin n => (s.getD i 1 : Rat)) * A := by
  apply Matrix.ext
  intro i j
  simpa only [Matrix.diagonal_mul] using
    Polynomial.allFin n _ (Polynomial.allFin n _ h i) j

/-- Cancellation for the rational term form. -/
theorem value (D : Nat) (a d : Rat) (hD : 0 < D) (h : (D : Rat) * a = d) :
    a = d / D := by
  apply (eq_div_iff (by exact_mod_cast hD.ne')).mpr
  simpa only [mul_comm] using h

end HexMatrixMathlib.DetPoly.Scaling
