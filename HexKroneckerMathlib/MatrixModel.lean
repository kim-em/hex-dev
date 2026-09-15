/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.ModSound
public import HexMatrixMathlib.Packed

public section

namespace Hex.Kronecker

/-- Polynomial dot product with the same list recursion as the checker. -/
@[expose] noncomputable def polyDot {k : Nat} : List (MvPolynomial (Fin k) Int) →
    List (MvPolynomial (Fin k) Int) → MvPolynomial (Fin k) Int
  | a::as, b::bs => a*b + polyDot as bs
  | _, _ => 0

theorem polyDot_bounded {cap k : Nat} {a b : List Bounds}
    {p q : List (MvPolynomial (Fin k) Int)}
    (ha : List.Forall₂ (Bounded cap) a p) (hb : List.Forall₂ (Bounded cap) b q) :
    Bounded cap (dotBounds cap k a b) (polyDot p q) := by
  induction ha generalizing b q with
  | nil => cases hb <;> exact Bounded.zero cap k
  | cons h ht ih =>
      cases hb with
      | nil => exact Bounded.zero cap k
      | cons g gt => exact (h.mul g).add (ih gt)

theorem polyDot_eval {k : Nat} (v : Fin k → Int) (a b : List (MvPolynomial (Fin k) Int)) :
    MvPolynomial.eval₂Hom (RingHom.id Int) v (polyDot a b) =
      Hex.Matrix.Packed.dotInt (a.map (MvPolynomial.eval₂Hom (RingHom.id Int) v))
        (b.map (MvPolynomial.eval₂Hom (RingHom.id Int) v)) := by
  induction a generalizing b with
  | nil => cases b <;> simp only [polyDot, map_zero, List.map_nil, Hex.Matrix.Packed.dotInt]
  | cons a as ih =>
      cases b <;> simp only [polyDot, map_zero, map_add, map_mul,
        List.map_cons, List.map_nil, Hex.Matrix.Packed.dotInt, ih]
      rfl

theorem dotValue_eq (mode : MulMode) (s : SizeBound) (r : Nat) (a b : List Int)
    (h : dotValid mode s r a b = true) : dotValue mode s r a b = Hex.Matrix.Packed.dotInt a b := by
  cases mode with
  | plain => rfl
  | signedPacked =>
      simp only [dotValid, Bool.and_eq_true_iff] at h
      exact HexMatrixMathlib.dotIntPacked_eq _ _ _ _ _ (eq_of_beq h.1.1.1.2)
        ((HexMatrixMathlib.allAbsLt_iff _ _).mp h.1.1.2)
        ((HexMatrixMathlib.allAbsLt_iff _ _).mp h.1.2)
        (by simpa only [Nat.mul_assoc] using of_decide_eq_true h.2)

end Hex.Kronecker
