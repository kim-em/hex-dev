/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries.Newton

public section

/-!
Newton inversion for fixed-precision truncated series.

The witness-taking operation is primary: it performs the bounded Newton update
`b ↦ b * (2 - a*b)` without checking the witness.  The optional wrapper
consults `UnitOps` only at positive precision and therefore correctly treats
precision zero as the one-element zero ring.
-/

namespace Hex.TSeries

universe u

variable {R : Type u} {n : Nat}

/-- One bounded Newton inverse update. -/
@[expose]
def invStep [Lean.Grind.CommRing R] (a b : TSeries R n)
    (m : Nat) : TSeries R n :=
  mulUpTo m b (C (1 + 1) - mulUpTo m a b)

/-- Invert through coefficient `m - 1`, zeroing all later stored
coefficients. -/
@[expose]
def invUpTo [Lean.Grind.CommRing R] (m : Nat)
    (a : TSeries R n) (u : R) : TSeries R n :=
  let b := newton (invStep a) (C u) (steps (min m n))
  ofFn fun i => if i < m then b.coeff i else 0

/-- The inverse of `a`, given an inverse of its constant coefficient. -/
@[expose]
def invOfUnit [Lean.Grind.CommRing R] (a : TSeries R n) (u : R) : TSeries R n :=
  invUpTo n a u

/-- Look up a constant-coefficient inverse and invert the series. -/
def inv? [Lean.Grind.CommRing R] [UnitOps R]
    (a : TSeries R n) : Option (TSeries R n) :=
  if n = 0 then
    some 0
  else
    match UnitOps.inv? (R := R) (a.coeff 0) with
    | some u => some (invOfUnit a u)
    | none => none

private def invError [Lean.Grind.CommRing R]
    (a b : TSeries R n) : TSeries R n :=
  1 - a * b

private theorem C_two [Lean.Grind.CommRing R] :
    (C (1 + 1) : TSeries R n) = 1 + 1 := by
  apply ext
  intro i hi
  rw [coeff_C _ i hi, coeff_add 1 1 i hi]
  split <;> grind

private theorem invInit_correct [Lean.Grind.CommRing R]
    (a : TSeries R n) (u : R) (hu : a.coeff 0 * u = 1) :
    Agree 1 (invError a (C u)) 0 := by
  intro i hi hip
  have hi0 : i = 0 := by omega
  subst i
  rw [show invError a (C u) = 1 - a * C u from rfl,
    coeff_sub 1 (a * C u) 0 hi, coeff_one 0 hi,
    coeff_mul a (C u) 0 hi, coeff_zero]
  unfold convCoeff
  simp only [Nat.zero_sub]
  rw [coeff_C u 0 hi]
  grind

private theorem invStep_agree [Lean.Grind.CommRing R]
    (a b : TSeries R n) (m : Nat) :
    Agree m (invStep a b m) (b * (C (1 + 1) - a * b)) := by
  unfold invStep
  exact (Agree.mulUpTo m b (C (1 + 1) - mulUpTo m a b)).trans
    (Agree.mul (Agree.refl m b)
      (Agree.sub (Agree.refl m (C (1 + 1))) (Agree.mulUpTo m a b)))

private theorem invError_step [Lean.Grind.CommRing R]
    (a b : TSeries R n) :
    invError a (b * (C (1 + 1) - a * b)) =
      invError a b * invError a b := by
  unfold invError
  rw [C_two]
  grind

private theorem invStep_correct [Lean.Grind.CommRing R]
    (a b : TSeries R n) (p m : Nat) (hpm : p + p ≤ m)
    (h : Agree p (invError a b) 0) :
    Agree (p + p) (invError a (invStep a b m)) 0 := by
  have hstep := (invStep_agree a b m).mono hpm
  have herr : Agree (p + p) (invError a (invStep a b m))
      (invError a (b * (C (1 + 1) - a * b))) :=
    Agree.sub (Agree.refl (p + p) 1)
      (Agree.mul (Agree.refl (p + p) a) hstep)
  rw [invError_step] at herr
  exact herr.trans (Agree.zeroMul h h)

private theorem invNewton_correct [Lean.Grind.CommRing R]
    (a : TSeries R n) (u : R) (hu : a.coeff 0 * u = 1) (j : Nat) :
    Agree (2 ^ j) (invError a (newton (invStep a) (C u) j)) 0 := by
  induction j with
  | zero => simpa [newton] using invInit_correct a u hu
  | succ j ih =>
      have hp : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by
        rw [Nat.pow_succ]
        omega
      change Agree (2 ^ (j + 1))
        (invError a (invStep a (newton (invStep a) (C u) j) (2 ^ (j + 1)))) 0
      have hs := invStep_correct a _ (2 ^ j) (2 ^ (j + 1))
        (Nat.le_of_eq hp) ih
      rw [hp] at hs
      exact hs

private theorem invUpTo_correct [Lean.Grind.CommRing R]
    (m : Nat) (a : TSeries R n) (u : R) (hu : a.coeff 0 * u = 1) :
    Agree (min m n) (invError a (invUpTo m a u)) 0 := by
  let p := min m n
  let b := newton (invStep a) (C u) (steps p)
  have hnewton : Agree (2 ^ steps p) (invError a b) 0 :=
    invNewton_correct a u hu (steps p)
  have hwrap : Agree p (invUpTo m a u) b := by
    intro i hi hip
    unfold invUpTo
    rw [coeff_ofFn _ i hi, ite_eq_left (by
      change i < min m n at hip
      omega)]
  have herr : Agree p (invError a (invUpTo m a u)) (invError a b) :=
    Agree.sub (Agree.refl p 1) (Agree.mul (Agree.refl p a) hwrap)
  exact herr.trans (hnewton.mono (two_pow_steps_ge p))

private theorem agreeOne [Lean.Grind.CommRing R] {p : Nat}
    {a : TSeries R n} (h : Agree p (1 - a) 0) : Agree p a 1 := by
  intro i hi hip
  have hz := h i hi hip
  rw [coeff_sub 1 a i hi, coeff_zero] at hz
  rw [coeff_one i hi]
  grind

private theorem agreeInv_unique [Lean.Grind.CommRing R] {p : Nat}
    {a b c : TSeries R n} (hb : Agree p (a * b) 1)
    (hc : Agree p (a * c) 1) : Agree p b c := by
  have hleft : Agree p (b * 1) (b * (a * c)) :=
    Agree.mul (Agree.refl p b) hc.symm
  have hright : Agree p ((a * b) * c) (1 * c) :=
    Agree.mul hb (Agree.refl p c)
  intro i hi hip
  calc
    b.coeff i = (b * 1).coeff i :=
      congrArg (fun x : TSeries R n => x.coeff i) (mul_one b).symm
    _ = (b * (a * c)).coeff i := hleft i hi hip
    _ = ((a * b) * c).coeff i :=
      congrArg (fun x : TSeries R n => x.coeff i) (by
        rw [← mul_assoc, mul_comm b a])
    _ = (1 * c).coeff i := hright i hi hip
    _ = c.coeff i :=
      congrArg (fun x : TSeries R n => x.coeff i) (one_mul c)

/-- Bounded inversion agrees with full inversion below its requested bound. -/
theorem coeff_invUpTo [Lean.Grind.CommRing R] (m : Nat)
    (a : TSeries R n) (u : R) (hu : a.coeff 0 * u = 1)
    (i : Nat) (hi : i < n) :
    (invUpTo m a u).coeff i =
      if i < m then (invOfUnit a u).coeff i else 0 := by
  split
  · rename_i him
    have hbounded := agreeOne (invUpTo_correct m a u hu)
    have hfullN : Agree n (a * invOfUnit a u) 1 := by
      simpa only [Nat.min_self, invOfUnit] using
        agreeOne (invUpTo_correct n a u hu)
    have hfull := hfullN.mono (Nat.min_le_right m n)
    exact agreeInv_unique hbounded hfull i hi (by omega)
  · rename_i him
    unfold invUpTo
    rw [coeff_ofFn _ i hi, ite_eq_right him]

/-- Newton inversion satisfies the defining multiplicative equation. -/
theorem invOfUnit_mul [Lean.Grind.CommRing R] (a : TSeries R n) (u : R)
    (hu : a.coeff 0 * u = 1) : a * invOfUnit a u = 1 := by
  have h : Agree n (a * invOfUnit a u) 1 := by
    simpa only [Nat.min_self, invOfUnit] using
      agreeOne (invUpTo_correct n a u hu)
  apply Agree.full (p := n) h
  omega

/-- A multiplicative inverse with the supplied constant witness is unique. -/
theorem invOfUnit_unique [Lean.Grind.CommRing R] (a b : TSeries R n) (u : R)
    (hu : a.coeff 0 * u = 1) (hb : a * b = 1) : b = invOfUnit a u := by
  calc
    b = b * 1 := (mul_one b).symm
    _ = b * (a * invOfUnit a u) := by rw [invOfUnit_mul a u hu]
    _ = (b * a) * invOfUnit a u := (mul_assoc _ _ _).symm
    _ = (a * b) * invOfUnit a u := by rw [mul_comm b a]
    _ = 1 * invOfUnit a u := by rw [hb]
    _ = invOfUnit a u := one_mul _

/-- Optional inversion succeeds exactly for units of the truncated-series
ring, including the unconditional precision-zero case. -/
theorem inv?_isSome_iff [Lean.Grind.CommRing R]
    [UnitOps R] [LawfulUnitOps R] (a : TSeries R n) :
    (inv? a).isSome = true ↔ n = 0 ∨ ∃ u, a.coeff 0 * u = 1 := by
  by_cases hn : n = 0
  · simp [inv?, hn]
  · rw [show inv? a =
      match UnitOps.inv? (R := R) (a.coeff 0) with
      | some u => some (invOfUnit a u)
      | none => none by simp [inv?, hn]]
    cases hq : UnitOps.inv? (R := R) (a.coeff 0) with
    | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, false_iff, hn, false_or]
        intro hunit
        have hsome := LawfulUnitOps.inv?_isSome (R := R) (a.coeff 0) hunit
        simp [hq] at hsome
    | some u =>
        simp only [Option.isSome_some, hn, false_or, true_iff]
        exact ⟨u, LawfulUnitOps.inv?_eq (R := R) (a.coeff 0) u hq⟩

end Hex.TSeries
