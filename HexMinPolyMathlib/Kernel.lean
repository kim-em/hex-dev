/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexMinPolyMathlib.Krylov
public import HexMinPolyMathlib.Basic

public import Batteries.Data.Vector.Lemmas

public section

/-! Transport of arbitrary accepted list certificates to Mathlib minimal polynomials. -/

namespace HexMinPolyMathlib

open Hex.Matrix Hex.Matrix.Lists Hex.Matrix.MinPolyLists HexMatrixMathlib HexPolyMathlib

local instance : Lean.Grind.Field ℚ := Field.toGrindField

/-- Decode one order without running its producer. -/
@[expose] noncomputable def decodeOrder (n : Nat) (o : OrderWitness) : OrderCert ℚ n :=
  ⟨decodeBlock o.poly, o.deg, inverseMatrix n o.deg o.inv⟩

/-- Decode the six polynomial blocks of an LCM step. -/
@[expose] noncomputable def decodeStep (s : LcmWitness) : LcmStep ℚ :=
  ⟨decodeBlock s.common, decodeBlock s.left, decodeBlock s.right,
    decodeBlock s.bezoutLeft, decodeBlock s.bezoutRight, decodeBlock s.result⟩

/-- The reference certificate corresponding to supplied list data. -/
@[expose] noncomputable def decodeWitness (n : Nat) (c : MinPolyWitness) : MinPolyCert ℚ n :=
  ⟨decodeBlock c.poly, Vector.ofFn (fun i => decodeOrder n (entry default c.order i)),
    Vector.ofFn (fun i => decodeStep (entry default c.steps i))⟩

theorem decode_order {n : Nat} (c : MinPolyWitness) (i : Fin n) :
    (decodeWitness n c).order.get i = decodeOrder n (entry default c.order i) := by
  exact Vector.get_ofFn _ _

theorem decode_step {n : Nat} (c : MinPolyWitness) (i : Fin n) :
    (decodeWitness n c).steps.get i = decodeStep (entry default c.steps i) := by
  exact Vector.get_ofFn _ _

/-- The running polynomial before a fold index. -/
@[expose] def runningAt (first : Scaled) (steps : List LcmWitness) : Nat → Scaled
  | 0 => first
  | k + 1 => (entry default steps k).result

theorem steps_spec (final first : Scaled) (orders : List OrderWitness) (steps : List LcmWitness)
    (hp : 0 < first.denom) (h : stepsCheck final first orders steps = true) :
    (∀ k, k ≤ orders.length → 0 < (runningAt first steps k).denom) ∧
    (∀ k, k < orders.length → stepCheck (runningAt first steps k)
      (entry default orders k).poly (entry default steps k) = true) ∧
    eqPoly final (runningAt first steps orders.length) = true := by
  induction orders generalizing first steps with
  | nil =>
    cases steps with
    | nil =>
      refine ⟨?_, fun k hk => by simp at hk, h⟩
      intro k hk
      have : k = 0 := by simpa using hk
      subst k
      exact hp
    | cons s ss => simp [stepsCheck] at h
  | cons o os ih =>
    cases steps with
    | nil => simp [stepsCheck] at h
    | cons s ss =>
      simp only [stepsCheck, Bool.and_eq_true] at h
      have hs := h.1
      simp only [stepCheck, Bool.and_assoc, Bool.and_eq_true] at hs
      have hr := valid_pos _ hs.2.2.2.2.2.1
      obtain ⟨hpos, hsteps, hfinal⟩ := ih s.result ss hr h.2
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        cases k with
        | zero => exact hp
        | succ k =>
          have hh := hpos k (by simpa using hk)
          cases k <;> exact hh
      · intro k hk
        cases k with
        | zero => exact h.1
        | succ k =>
          have hh := hsteps k (by simpa using hk)
          cases k <;> exact hh
      · cases os with
        | nil => exact hfinal
        | cons o os => exact hfinal

theorem decode_running {n : Nat} (c : MinPolyWitness) (j : Nat) (hj : j ≤ n) :
    (decodeWitness n c).running j hj = decodeBlock (runningAt ⟨1, [1]⟩ c.steps j) := by
  cases j with
  | zero =>
    change (1 : Hex.DensePoly ℚ) = decodeBlock ⟨1, [1]⟩
    apply equiv.injective
    change toPolynomial (1 : Hex.DensePoly ℚ) = toPolynomial (decodeBlock ⟨1, [1]⟩)
    rw [← blockPolynomial_eq]
    simp [blockPolynomial, decodeList, decodeScalar, polynomialOfList]
  | succ j =>
    simp only [MinPolyCert.running, decodeWitness, Vector.get_ofFn, decodeStep, runningAt]

theorem reference_check {n : Nat} (rows : List (List Rat)) (c : MinPolyWitness)
    (h : checkMinPolyList n rows c = true) :
    (decodeWitness n c).check (inputMatrix n c.input) = true := by
  simp only [checkMinPolyList, Bool.and_assoc, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hd, hz, _, ho, _, hv, hm, horders, hsteps⟩ := h
  obtain ⟨hpos, hstep, hfinal⟩ := steps_spec c.poly ⟨1, [1]⟩ c.order c.steps (by decide) hsteps
  rw [ho] at hpos hstep hfinal
  unfold MinPolyCert.check
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro i _
    have hi := (all_iff _ _).mp horders i i.isLt
    simp only [orderCheck, Bool.and_assoc, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hi
    obtain ⟨_, hv, hm, hl, hden, _, ha, hinv⟩ := hi
    rw [decode_order]
    simp only [decodeOrder]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact (decodeBlock_size _ hv).trans hl
    · rw [decodeBlock_coeff, decodeScalar]
      have hh := of_decide_eq_true hm
      rw [hl] at hh
      simp only [Nat.add_sub_cancel] at hh
      rw [hh, Int.ofNat_eq_natCast, Int.cast_natCast, div_self]
      exact_mod_cast (Nat.ne_of_gt (valid_pos _ hv))
    · exact annihilation_of_check c.input hz hd i _ hv hl ha
    · exact checkRightInverse_complete _ _ (rightInverse_of_check c.input hz hd i _ hden hinv)
  · intro j _
    have hj := (all_iff _ _).mp horders j j.isLt
    simp only [orderCheck, Bool.and_assoc, Bool.and_eq_true] at hj
    have hs := stepCheck_sound _ _ _ (hpos j (by omega)) (valid_pos _ hj.2.1)
      (hstep j j.isLt)
    rw [decode_running]
    simp only [decode_step, decode_order, decodeStep, decodeOrder]
    rcases hs with ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    all_goals apply equiv.injective
    all_goals simp only [equiv_apply, toPolynomial_add, toPolynomial_mul, ← blockPolynomial_eq]
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · rw [decode_running]
    apply equiv.injective
    change toPolynomial (decodeBlock c.poly) = toPolynomial (decodeBlock _)
    simpa only [← blockPolynomial_eq] using
      eqPoly_sound _ _ (valid_pos _ hv) (hpos n (by omega)) hfinal
  · change (decodeBlock c.poly).coeff ((decodeBlock c.poly).size - 1) = 1
    rw [decodeBlock_size _ hv, decodeBlock_coeff, decodeScalar]
    rw [of_decide_eq_true hm, Int.ofNat_eq_natCast, Int.cast_natCast, div_self]
    exact_mod_cast (Nat.ne_of_gt (valid_pos _ hv))

/-- The reference certificate proves the Mathlib statement without any
hypothesis connecting the witness to the producer. -/
theorem equiv_of_check {F : Type*} [Field F] [DecidableEq F] {n : Nat}
    (A : Hex.Matrix F n n) (c : MinPolyCert F n) (h : c.check A = true) :
    equiv c.poly = minpoly F (matrixEquiv A) := by
  obtain ⟨hm, ha, hd⟩ := c.check_sound A h
  have hz : vectorEquiv (0 : Vector F n) = (0 : Fin n → F) := by
    funext i
    rw [vectorEquiv_apply]
    change (0 : Vector F n)[i.val] = 0
    rw [Vector.getElem_zero]
  apply minpoly.unique F (matrixEquiv A)
  · rw [Polynomial.Monic.def, equiv_apply, leadingCoeff_toPolynomial]
    exact hm
  · apply Matrix.ext_iff_mulVec.mpr
    intro w
    have he := vectorEquiv_evalVec c.poly A (vectorEquiv.symm w)
    rw [ha, hz, Equiv.apply_symm_apply] at he
    simpa using he.symm
  · intro q hq hroot
    have hall : ∀ v : Vector F n, evalVec (equiv.symm q) A v = 0 := by
      intro v
      apply vectorEquiv.injective
      rw [vectorEquiv_evalVec, RingEquiv.apply_symm_apply, hroot, Matrix.zero_mulVec, hz]
    have hpoly := toPolynomial_dvd (hd _ hall)
    exact Polynomial.degree_le_of_dvd (by simpa using hpoly) hq.ne_zero

/-- The polynomial claimed by the initial rational certificate. -/
@[expose] noncomputable def decodePoly (c : MinPolyWitness) : Polynomial ℚ :=
  blockPolynomial c.poly

/-- The soundness boundary for rational literal minimal-polynomial tactics. -/
theorem minpoly_eq_of_checkList {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ)
    (rows : List (List Rat)) (c : MinPolyWitness) (hA : A = ofLists n n rows)
    (hc : checkMinPolyList n rows c = true) : minpoly ℚ A = decodePoly c := by
  have h := hc
  simp only [checkMinPolyList, Bool.and_assoc, Bool.and_eq_true, Nat.blt_eq] at h
  have hr := scaleRows_sound c.input.denom rows c.input.nums h.1 h.2.2.1
  have hi : matrixEquiv (inputMatrix n c.input) = A := by
    rw [inputMatrix, Equiv.apply_symm_apply, hA, hr]
  have he := equiv_of_check (inputMatrix n c.input) (decodeWitness n c) (reference_check rows c hc)
  rw [hi] at he
  change minpoly ℚ A = blockPolynomial c.poly
  rw [blockPolynomial_eq]
  exact he.symm

/-- Shared literal-layer result record for the term frontend. -/
abbrev MinPolyResult {n : Nat} (A : Matrix (Fin n) (Fin n) ℚ) :=
  Certified (fun M => minpoly ℚ M) A

/-- Compare the computed block with the polynomial adapter's coefficients. -/
theorem eq_target (c : MinPolyWitness) (hp : 0 < c.poly.denom)
    (p : Polynomial ℚ) (qs : List Rat) (s : Scaled)
    (hs : 0 < s.denom) (hscale : scaleRow s.denom qs s.nums = true)
    (he : eqPoly c.poly s = true) (hpoly : p = polynomialOfList qs) :
    decodePoly c = p := by
  rw [hpoly, scaleRow_sound s.denom qs s.nums hs hscale]
  exact eqPoly_sound c.poly s hp hs he

theorem checked_pos {n : Nat} (rows : List (List Rat)) (c : MinPolyWitness)
    (h : checkMinPolyList n rows c = true) : 0 < c.poly.denom := by
  simp only [checkMinPolyList, Bool.and_assoc, Bool.and_eq_true] at h
  exact valid_pos _ h.2.2.2.2.2.1

end HexMinPolyMathlib
