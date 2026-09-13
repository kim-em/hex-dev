/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRankMathlib.Polynomial
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Ring.Hom.InjSurj

public section

namespace HexMatrixMathlib.PolyWitness

open Polynomial Hex.Matrix.PolyWitness

variable {R : Type*} [CommRing R] [Nontrivial R]

omit [Nontrivial R] in
private theorem cast_polynomial (a : Int) : (a : Polynomial R) = C (a : R) :=
  (map_intCast (C : R →+* Polynomial R) a).symm

/-- A coefficient list with nonzero last coefficient has the expected degree
and leading coefficient, also over rings with zero divisors. -/
theorem polynomial_spec (f : List Int) (hf : (f.getLastD 0 : R) ≠ 0) :
    (eval (X : Polynomial R) f).degree = (f.length - 1 : Nat) ∧
      (eval (X : Polynomial R) f).leadingCoeff = (f.getLastD 0 : R) := by
  induction f with
  | nil => simp at hf
  | cons a as ih =>
    cases as with
    | nil =>
      have ha : (a : R) ≠ 0 := by simpa using hf
      simp only [eval_cons, eval_nil, mul_zero, add_zero]
      simp only [cast_polynomial]
      rw [Polynomial.degree_C ha, Polynomial.leadingCoeff_C]
      simp
    | cons b bs =>
      have ht : ((b :: bs).getLastD 0 : R) ≠ 0 := by simpa using hf
      obtain ⟨hdeg, hlc⟩ := ih ht
      have hlt : (C (a : R)).degree < (X * eval (X : Polynomial R) (b :: bs)).degree := by
        rw [mul_comm X, Polynomial.degree_mul_X, hdeg]
        exact lt_of_le_of_lt degree_C_le (by simp only [List.length_cons, Nat.add_sub_cancel]; exact_mod_cast Nat.succ_pos bs.length)
      have heq : eval (X : Polynomial R) (a :: b :: bs) =
          C (a : R) + X * eval X (b :: bs) := by rw [eval_cons, cast_polynomial]
      rw [heq]
      rw [Polynomial.degree_add_eq_right_of_degree_lt hlt,
        Polynomial.leadingCoeff_add_of_degree_lt hlt, mul_comm X, Polynomial.degree_mul_X,
        Polynomial.leadingCoeff_mul_X, hdeg, hlc]
      simp

omit [Nontrivial R] in
/-- Interpret the same coefficient list before or after a coefficient-ring homomorphism. -/
theorem eval_polynomial (x : R) (f : List Int) :
    Polynomial.eval x (eval (X : Polynomial R) f) = eval x f := by
  induction f with
  | nil => simp
  | cons a as ih => simp [ih]

omit [Nontrivial R] in
/-- Coefficients of the polynomial denoted by an integer list. -/
theorem coeff_polynomial (f : List Int) (n : Nat) :
    (eval (X : Polynomial R) f).coeff n = (f.getD n 0 : R) := by
  induction f generalizing n with
  | nil => simp
  | cons a as ih =>
    have heq : eval (X : Polynomial R) (a :: as) = C (a : R) + X * eval X as := by
      rw [eval_cons]
      exact congrArg (· + X * eval X as) (map_intCast (C : R →+* Polynomial R) a).symm
    rw [heq]
    cases n with
    | zero => simp
    | succ n =>
      rw [Polynomial.coeff_add, Polynomial.coeff_C, ite_eq_right (Nat.succ_ne_zero n),
        Polynomial.coeff_X_mul, ih, zero_add, List.getD_cons_succ]

omit [Nontrivial R] in
theorem eval₂_polynomial {S : Type*} [CommRing S] (φ : R →+* S) (x : S) (f : List Int) :
    Polynomial.eval₂ φ x (eval (X : Polynomial R) f) = eval x f := by
  induction f with
  | nil => simp
  | cons a as ih =>
    have hc : Polynomial.eval₂ φ x (a : Polynomial R) = (a : S) :=
      map_intCast (Polynomial.eval₂RingHom φ x) a
    simp only [eval_cons, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, ih, hc]

/-- The monic associate of the defining polynomial modulo the witness modulus. -/
noncomputable def modPolynomial (M : Nat) (f : List Int) (u : Int) : Polynomial (ZMod M) :=
  C (u : ZMod M) * eval X f

/-- The modular ring used for the lower-bound certificate. -/
abbrev ModQuot (M : Nat) (f : List Int) (u : Int) := AdjoinRoot (modPolynomial M f u)

theorem leadingInverse (M : Nat) (f : List Int) (u : Int)
    (h : eqMod M [Int.mul (f.getLastD 0) u] [1] = true) :
    (f.getLastD 0 : ZMod M) * (u : ZMod M) = 1 := by
  have := eqMod_sound (0 : ZMod M) M (by simp) _ _ h
  simp only [eval_cons, eval_nil, mul_zero, add_zero, Int.cast_one] at this
  have heq : Int.mul (f.getLastD 0) u = f.getLastD 0 * u := rfl
  simpa [heq] using this

/-- A unit leading coefficient and positive degree suffice for a nontrivial
modular quotient. Neither primality nor irreducibility is assumed. -/
theorem modQuot_nontrivial (M : Nat) (f : List Int) (u : Int) (hM : 1 < M)
    (hf : 1 < f.length) (hu : eqMod M [Int.mul (f.getLastD 0) u] [1] = true) :
    Nontrivial (ModQuot M f u) := by
  let : Fact (1 < M) := ⟨hM⟩
  have hi := leadingInverse M f u hu
  have hu' : IsUnit (u : ZMod M) := IsUnit.of_mul_eq_one_right _ hi
  have hlc : (f.getLastD 0 : ZMod M) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hi
    exact zero_ne_one hi
  obtain ⟨hdeg, hlead⟩ := polynomial_spec f hlc
  have hmonic : (modPolynomial M f u).Monic := by
    change (C (u : ZMod M) * eval X f).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_C_mul_of_isUnit hu', hlead, mul_comm]
    exact hi
  apply (AdjoinRoot.nontrivial_iff_of_monic hmonic).mpr
  rw [modPolynomial, Polynomial.degree_C_mul_of_isUnit hu', hdeg]
  exact_mod_cast Nat.sub_pos_of_lt hf

/-- The modular characteristic vanishes in the polynomial quotient. -/
theorem modQuot_char (M : Nat) (f : List Int) (u : Int) :
    (M : ModQuot M f u) = 0 := by
  calc
    (M : ModQuot M f u) = AdjoinRoot.of (modPolynomial M f u) (M : ZMod M) :=
      (map_natCast _ M).symm
    _ = 0 := by rw [ZMod.natCast_self, map_zero]

/-- The original, possibly nonmonic defining polynomial vanishes at the
modular root, since its leading coefficient is a unit modulo the modulus. -/
theorem modRoot_eval (M : Nat) (f : List Int) (u : Int)
    (hu : eqMod M [Int.mul (f.getLastD 0) u] [1] = true) :
    eval (AdjoinRoot.root (modPolynomial M f u)) f = 0 := by
  let g := modPolynomial M f u
  have hi := congrArg (AdjoinRoot.of g) (leadingInverse M f u hu)
  have hi' : (f.getLastD 0 : AdjoinRoot g) * (u : AdjoinRoot g) = 1 := by
    simpa using hi
  have hrel := AdjoinRoot.eval₂_root g
  change Polynomial.eval₂ (AdjoinRoot.of g) (AdjoinRoot.root g)
    (C (u : ZMod M) * eval X f) = 0 at hrel
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, eval₂_polynomial] at hrel
  have hrel' : (u : AdjoinRoot g) * eval (AdjoinRoot.root g) f = 0 := by simpa using hrel
  have h := congrArg (fun z : AdjoinRoot g => (f.getLastD 0 : AdjoinRoot g) * z) hrel'
  rwa [← mul_assoc, hi', one_mul, mul_zero] at h

/-- The integral model of a fixed algebraic presentation. Monicity is not
required: division witnesses are checked before taking the quotient. -/
abbrev IntQuot (f : List Int) := AdjoinRoot (eval (X : Polynomial Int) f)

/-- Modular reduction of the integral model. -/
noncomputable def modHom (M : Nat) (f : List Int) (u : Int)
    (hu : eqMod M [Int.mul (f.getLastD 0) u] [1] = true) : IntQuot f →+* ModQuot M f u :=
  AdjoinRoot.lift (Int.castRingHom _) (AdjoinRoot.root (modPolynomial M f u))
    (by rw [eval₂_polynomial]; exact modRoot_eval M f u hu)

omit [Nontrivial R] in
/-- A polynomial certificate transfers through an injective interpretation
of the integral model, including into a number field. -/
theorem rank_eq_embedded [IsDomain R] [CharZero R] (f : List Int)
    (ev : IntQuot f →+* R) (hev : Function.Injective ev) (x : R)
    (hx : ev (AdjoinRoot.root (eval (X : Polynomial Int) f)) = x)
    (n m : Nat) (L : List (List (List Int))) (c : Hex.Matrix.PolyWitness)
    (h : Hex.Matrix.checkRankPoly n m f L c = true) : (ofPolys x n m L).rank = c.rank := by
  let : IsDomain (IntQuot f) := Function.Injective.isDomain ev hev
  let : CharZero (IntQuot f) := ⟨fun i j hij => by
    apply Nat.cast_injective (R := R)
    simpa only [map_natCast] using congrArg ev hij⟩
  have h' := h
  simp only [Hex.Matrix.checkRankPoly, Bool.and_eq_true, and_assoc] at h'
  obtain ⟨_, _, hM, hdeg, hu, _⟩ := h'
  let : Nontrivial (ModQuot c.modulus f c.leadingInv) :=
    modQuot_nontrivial c.modulus f c.leadingInv (by simpa using hM) (by simpa using hdeg) hu
  let root := AdjoinRoot.root (eval (X : Polynomial Int) f)
  have hf : eval root f = 0 := by
    rw [← eval₂_polynomial (AdjoinRoot.of _) root f]
    exact AdjoinRoot.eval₂_root _
  have hr := rank_eq_of_check (modHom c.modulus f c.leadingInv hu) root n m f L c hf
    (modQuot_char c.modulus f c.leadingInv) h
  have hmap : (ofPolys root n m L).map ev = ofPolys x n m L := by
    ext i j
    simp only [Matrix.map_apply, ofPolys_apply, map_eval, root, hx]
  rw [← hmap, rank_map_of_injective ev hev]
  exact hr

end HexMatrixMathlib.PolyWitness
