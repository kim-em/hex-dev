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

theorem checkRow_entry (mode : MulMode) (s : SizeBound) (r : Nat) (a : List Int)
    (cols : List (List Int)) (cs : List Int) (h : checkRow mode s r a cols cs = true)
    (j : Nat) (hj : j < cols.length) :
    Hex.Matrix.Packed.dotInt a (cols.getD j []) = cs.getD j 0 := by
  induction cols generalizing cs j with
  | nil => simp at hj
  | cons b bs ih =>
      cases cs with
      | nil => simp [checkRow] at h
      | cons c cs =>
          have h := Bool.and_eq_true_iff.mp h
          have hv := (Bool.and_eq_true_iff.mp h.1).1
          have he := eq_of_beq (Bool.and_eq_true_iff.mp h.1).2
          cases j with
          | zero => simpa only [List.getD_cons_zero, dotValue_eq mode s r a b hv] using he
          | succ j => exact ih cs h.2 j (by simpa using hj)

theorem checkRows_entry (mode : MulMode) (s : SizeBound) (r : Nat)
    (cols as cs : List (List Int)) (h : checkRows mode s r cols as cs = true)
    (i j : Nat) (hi : i < as.length) (hj : j < cols.length) :
    Hex.Matrix.Packed.dotInt (as.getD i []) (cols.getD j []) = (cs.getD i []).getD j 0 := by
  induction as generalizing cs i with
  | nil => simp at hi
  | cons a as ih =>
      cases cs with
      | nil => simp [checkRows] at h
      | cons c cs =>
          have h := Bool.and_eq_true_iff.mp h
          cases i with
          | zero => exact checkRow_entry mode s r a cols c h.1 j hj
          | succ i => exact ih cs h.2 i (by simpa using hi)

theorem checkRowMod_entry (mode : MulMode) (s : SizeBound) (r p : Nat) (a : List Int)
    (cols : List (List Int)) (cs qs : List Int) (h : checkRowMod mode s r p a cols cs qs = true)
    (j : Nat) (hj : j < cols.length) :
    Hex.Matrix.Packed.dotInt a (cols.getD j []) - cs.getD j 0 = (p:Int)*qs.getD j 0 := by
  induction cols generalizing cs qs j with
  | nil => simp at hj
  | cons b bs ih =>
      cases cs <;> cases qs <;> try (simp only [checkRowMod, Bool.false_eq_true] at h)
      rename_i c cs q qs
      have h := Bool.and_eq_true_iff.mp h
      have hv := (Bool.and_eq_true_iff.mp h.1).1
      have he := eq_of_beq (Bool.and_eq_true_iff.mp h.1).2
      cases j with
      | zero => simpa only [List.getD_cons_zero, dotValue_eq mode s r a b hv] using he
      | succ j => exact ih cs qs h.2 j (by simpa using hj)

theorem checkRowsMod_entry (mode : MulMode) (s : SizeBound) (r p : Nat)
    (cols as cs qs : List (List Int)) (h : checkRowsMod mode s r p cols as cs qs = true)
    (i j : Nat) (hi : i < as.length) (hj : j < cols.length) :
    Hex.Matrix.Packed.dotInt (as.getD i []) (cols.getD j []) - (cs.getD i []).getD j 0 =
      (p:Int)*(qs.getD i []).getD j 0 := by
  induction as generalizing cs qs i with
  | nil => simp at hi
  | cons a as ih =>
      cases cs <;> cases qs <;> try (simp only [checkRowsMod, Bool.false_eq_true] at h)
      rename_i c cs q qs
      have h := Bool.and_eq_true_iff.mp h
      cases i with
      | zero => exact checkRowMod_entry mode s r p a cols c q h.1 j hj
      | succ i => exact ih cs qs h.2 i (by simpa using hi)

end Hex.Kronecker
