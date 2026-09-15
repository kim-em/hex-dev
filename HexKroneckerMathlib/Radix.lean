/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexKroneckerMathlib.Denote
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.GetD

public section

namespace Hex.Kronecker

open scoped BigOperators

/-- The exact size of the finite degree box, used only in proofs. -/
@[expose] def boxSize (ds : List Nat) : Nat := (ds.map (· + 1)).prod

theorem boxSize_pos (ds : List Nat) : 0 < boxSize ds := by
  induction ds with
  | nil => decide
  | cons d ds ih => exact Nat.mul_pos (Nat.succ_pos d) ih

@[simp] theorem length_makeStrides (s : Nat) (ds : List Nat) :
    (makeStrides s ds).length = ds.length := by
  induction ds generalizing s <;> simp [makeStrides, *]

theorem code_scale (s : Nat) (ds es : List Nat) :
    code (makeStrides s ds) es = s * code (makeStrides 1 ds) es := by
  induction ds generalizing s es with
  | nil => simp [makeStrides, code]
  | cons d ds ih =>
      cases es with
      | nil => simp [makeStrides, code]
      | cons e es =>
          simp only [makeStrides, code, Nat.one_mul]
          rw [ih (s * (d + 1)) es, ih (d + 1) es]
          ring

theorem code_cons (d e : Nat) (ds es : List Nat) :
    code (makeStrides 1 (d :: ds)) (e :: es) = e + (d + 1) * code (makeStrides 1 ds) es := by
  simp only [makeStrides, code, Nat.one_mul, Nat.mul_one]
  rw [code_scale]

theorem code_lt {ds es : List Nat} (h : List.Forall₂ (· ≤ ·) es ds) :
    code (makeStrides 1 ds) es < boxSize ds := by
  induction h with
  | nil => simp [makeStrides, code, boxSize]
  | @cons e d es ds he ht ih =>
      rw [code_cons]
      change e + (d + 1) * code (makeStrides 1 ds) es < (d + 1) * boxSize ds
      have hm := Nat.mul_le_mul_left (d + 1) (Nat.succ_le_of_lt ih)
      rw [Nat.mul_succ] at hm
      omega

/-- Mixed-radix codes distinguish exponent vectors inside the common box. -/
theorem code_inj {ds es fs : List Nat} (he : List.Forall₂ (· ≤ ·) es ds)
    (hf : List.Forall₂ (· ≤ ·) fs ds)
    (h : code (makeStrides 1 ds) es = code (makeStrides 1 ds) fs) : es = fs := by
  induction he generalizing fs with
  | nil => cases hf; rfl
  | @cons e d es ds he ht ih =>
      cases hf with
      | @cons f _ fs _ hf hft =>
          rw [code_cons, code_cons] at h
          have hhead : e = f := by
            have hm := congrArg (fun n => n % (d + 1)) h
            simpa [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (Nat.lt_succ_of_le he),
              Nat.mod_eq_of_lt (Nat.lt_succ_of_le hf)] using hm
          subst f
          have htail := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos d) (Nat.add_left_cancel h)
          rw [ih hft htail]

theorem code_ofFn {k : Nat} (ss : List Nat) (hs : ss.length = k) (e : Fin k → Nat) :
    code ss (List.ofFn e) = ∑ i, ss.getD i.val 0 * e i := by
  induction k generalizing ss with
  | zero =>
      have : ss = [] := List.length_eq_zero_iff.mp hs
      subst ss
      simp [code]
  | succ k ih =>
      cases ss with
      | nil => simp at hs
      | cons s ss =>
          have ht : ss.length = k := by simpa using hs
          simp only [List.ofFn_succ, code, Fin.sum_univ_succ, Fin.val_zero,
            List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ, ih ss ht]
          rw [Nat.mul_comm]

/-- Relate the finite variable model to the list degree box used by the checker. -/
theorem box_ofFn {k : Nat} (ds : List Nat) (hd : ds.length = k) (e : Fin k → Nat)
    (he : ∀ i, e i ≤ ds.getD i.val 0) : List.Forall₂ (· ≤ ·) (List.ofFn e) ds := by
  induction ds generalizing k with
  | nil =>
      have : k = 0 := by simpa using hd.symm
      subst k
      simp
  | cons d ds ih =>
      cases k with
      | zero => simp at hd
      | succ k =>
          rw [List.ofFn_succ]
          apply List.Forall₂.cons
          · simpa using he 0
          · apply ih (by simpa using hd) (fun i => e i.succ)
            intro i
            simpa using he i.succ

theorem eval₂_eq_code {k : Nat} (base : Int) (ss : List Nat) (hs : ss.length = k)
    (p : MvPolynomial (Fin k) Int) :
    MvPolynomial.eval₂Hom (RingHom.id Int) (fun i => base ^ ss.getD i.val 0) p =
      ∑ e ∈ p.support, p.coeff e * base ^ code ss (List.ofFn fun i => e i) := by
  classical
  change MvPolynomial.eval₂ _ _ _ = _
  rw [MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro e _
  simp only [RingHom.id_apply, ← pow_mul, Finset.prod_pow_eq_pow_sum, code_ofFn ss hs]

end Hex.Kronecker
