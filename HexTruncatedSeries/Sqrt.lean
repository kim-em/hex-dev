/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries.Inverse

public section

/-!
Newton lifting of a supplied constant square root.

The iteration lifts the inverse square root, avoiding an inversion inside each
step.  A single witness inverting `2*r` supplies both the initial inverse of
`r` and the inverse of `2`.  The optional wrapper treats precisions zero and
one separately, where no lifting inverse is needed.
-/

namespace Hex.TSeries

universe u

variable {R : Type u} {n : Nat}

/-- One bounded inverse-square-root Newton update. -/
@[expose]
def sqrtStep [Lean.Grind.CommRing R] (a : TSeries R n) (halfInv : R)
    (z : TSeries R n) (m : Nat) : TSeries R n :=
  let z2 := mulUpTo m z z
  let residual := C (1 + 1 + 1) - mulUpTo m a z2
  mulUpTo m (mulUpTo m z residual) (C halfInv)

/-- Lift the supplied root through a bounded precision. -/
@[expose]
def sqrtUpTo [Lean.Grind.CommRing R] (m : Nat)
    (a : TSeries R n) (r v : R) : TSeries R n :=
  let z0 : TSeries R n := C ((1 + 1) * v)
  let z := newton (sqrtStep a (r * v)) z0 (steps (min m n))
  let s := mulUpTo m a z
  ofFn fun i => if i < m then s.coeff i else 0

/-- The square root of `a` above `r`, given a witness inverting `2*r`. -/
@[expose]
def sqrtOfRoot [Lean.Grind.CommRing R]
    (a : TSeries R n) (r v : R) : TSeries R n :=
  sqrtUpTo n a r v

/-- Check the supplied constant root and look up the inverse needed to lift
it. -/
def sqrt? [Lean.Grind.CommRing R] [DecidableEq R] [UnitOps R]
    (a : TSeries R n) (r : R) : Option (TSeries R n) :=
  if n = 0 then
    some 0
  else if r * r ≠ a.coeff 0 then
    none
  else if n ≤ 1 then
    some (C r)
  else
    match UnitOps.inv? (R := R) ((1 + 1) * r) with
    | some v => some (sqrtOfRoot a r v)
    | none => none

private def sqrtError [Lean.Grind.CommRing R]
    (a z : TSeries R n) : TSeries R n :=
  1 - a * z * z

private theorem C_three [Lean.Grind.CommRing R] :
    (C (1 + 1 + 1) : TSeries R n) = 1 + 1 + 1 := by
  rw [C_add, C_add, C_one]

private theorem half_series [Lean.Grind.CommRing R] (h : R)
    (hh : (1 + 1) * h = 1) :
    (1 + 1 : TSeries R n) * C h = 1 := by
  calc
    (1 + 1 : TSeries R n) * C h = C (1 + 1) * C h := by
      rw [C_add, C_one]
    _ = C ((1 + 1) * h) := (C_mul _ _).symm
    _ = C 1 := by rw [hh]
    _ = 1 := C_one

private theorem sqrtInit_correct [Lean.Grind.CommRing R]
    (a : TSeries R n) (r v : R) (hr : r * r = a.coeff 0)
    (hv : ((1 + 1) * r) * v = 1) :
    Agree 1 (sqrtError a (C ((1 + 1) * v))) 0 := by
  intro i hi hip
  have hi0 : i = 0 := by omega
  subst i
  rw [show sqrtError a (C ((1 + 1) * v)) =
      1 - a * C ((1 + 1) * v) * C ((1 + 1) * v) from rfl,
    coeff_sub 1 _ 0 hi, coeff_one 0 hi,
    coeff_mul_zero (a * C ((1 + 1) * v)) (C ((1 + 1) * v)) hi,
    coeff_mul_zero a (C ((1 + 1) * v)) hi,
    coeff_C ((1 + 1) * v) 0 hi, coeff_zero]
  grind

private theorem sqrtStep_agree [Lean.Grind.CommRing R]
    (a z : TSeries R n) (h : R) (m : Nat) :
    Agree m (sqrtStep a h z m)
      (z * (C (1 + 1 + 1) - a * (z * z)) * C h) := by
  unfold sqrtStep
  have hz2 := Agree.mulUpTo m z z
  have hres : Agree m
      (C (1 + 1 + 1) - mulUpTo m a (mulUpTo m z z))
      (C (1 + 1 + 1) - a * (z * z)) :=
    Agree.sub (Agree.refl m _)
      ((Agree.mulUpTo m a (mulUpTo m z z)).trans
        (Agree.mul (Agree.refl m a) hz2))
  have hmid : Agree m
      (mulUpTo m z
        (C (1 + 1 + 1) - mulUpTo m a (mulUpTo m z z)))
      (z * (C (1 + 1 + 1) - a * (z * z))) :=
    (Agree.mulUpTo m _ _).trans (Agree.mul (Agree.refl m z) hres)
  exact (Agree.mulUpTo m _ (C h)).trans
    (Agree.mul hmid (Agree.refl m (C h)))

private theorem sqrtError_step [Lean.Grind.CommRing R]
    (a z : TSeries R n) (h : R) (hh : (1 + 1) * h = 1) :
    sqrtError a (z * (C (1 + 1 + 1) - a * (z * z)) * C h) =
      sqrtError a z * sqrtError a z *
        ((1 + 1 + 1 + sqrtError a z) * C h * C h) := by
  unfold sqrtError
  rw [C_three]
  have hs := half_series (n := n) h hh
  grind

private theorem sqrtStep_correct [Lean.Grind.CommRing R]
    (a z : TSeries R n) (h : R) (p m : Nat) (hpm : p + p ≤ m)
    (hh : (1 + 1) * h = 1) (hz : Agree p (sqrtError a z) 0) :
    Agree (p + p) (sqrtError a (sqrtStep a h z m)) 0 := by
  have hstep := (sqrtStep_agree a z h m).mono hpm
  have herr : Agree (p + p) (sqrtError a (sqrtStep a h z m))
      (sqrtError a (z * (C (1 + 1 + 1) - a * (z * z)) * C h)) :=
    Agree.sub (Agree.refl (p + p) 1)
      (Agree.mul
        (Agree.mul (Agree.refl (p + p) a) hstep) hstep)
  rw [sqrtError_step a z h hh] at herr
  have hz2 : Agree (p + p) (sqrtError a z * sqrtError a z) 0 :=
    Agree.zeroMul hz hz
  have hz3 : Agree (p + p)
      (sqrtError a z * sqrtError a z *
        ((1 + 1 + 1 + sqrtError a z) * C h * C h)) 0 := by
    simpa [zero_mul] using Agree.mul hz2
      (Agree.refl (p + p) ((1 + 1 + 1 + sqrtError a z) * C h * C h))
  exact herr.trans hz3

private theorem sqrtNewton_correct [Lean.Grind.CommRing R]
    (a : TSeries R n) (r v : R) (hr : r * r = a.coeff 0)
    (hv : ((1 + 1) * r) * v = 1) (j : Nat) :
    Agree (2 ^ j)
      (sqrtError a
        (newton (sqrtStep a (r * v)) (C ((1 + 1) * v)) j)) 0 := by
  have hh : (1 + 1) * (r * v) = 1 := by grind
  induction j with
  | zero => simpa [newton] using sqrtInit_correct a r v hr hv
  | succ j ih =>
      have hp : 2 ^ j + 2 ^ j = 2 ^ (j + 1) := by
        rw [Nat.pow_succ]
        omega
      change Agree (2 ^ (j + 1))
        (sqrtError a (sqrtStep a (r * v)
          (newton (sqrtStep a (r * v)) (C ((1 + 1) * v)) j)
          (2 ^ (j + 1)))) 0
      have hs := sqrtStep_correct a _ (r * v) (2 ^ j) (2 ^ (j + 1))
        (Nat.le_of_eq hp) hh ih
      rw [hp] at hs
      exact hs

private theorem sqrtStep_stable [Lean.Grind.CommRing R]
    (a z : TSeries R n) (h : R) (p m : Nat) (hpm : p ≤ m)
    (hh : (1 + 1) * h = 1) (hz : Agree p (sqrtError a z) 0) :
    Agree p (sqrtStep a h z m) z := by
  have hstep := (sqrtStep_agree a z h m).mono hpm
  have hid :
      z * (C (1 + 1 + 1) - a * (z * z)) * C h - z =
        z * sqrtError a z * C h := by
    unfold sqrtError
    rw [C_three]
    have hs := half_series (n := n) h hh
    grind
  have hzmul : Agree p (z * sqrtError a z * C h) 0 := by
    have hze : Agree p (z * sqrtError a z) 0 := by
      simpa [mul_zero] using Agree.mul (Agree.refl p z) hz
    simpa [zero_mul] using Agree.mul hze (Agree.refl p (C h))
  have hraw : Agree p
      (z * (C (1 + 1 + 1) - a * (z * z)) * C h) z := by
    apply Agree.ofSub
    rw [hid]
    exact hzmul
  exact hstep.trans hraw

private theorem sqrtNewton_stable [Lean.Grind.CommRing R]
    (a : TSeries R n) (r v : R) (hr : r * r = a.coeff 0)
    (hv : ((1 + 1) * r) * v = 1) (j : Nat) :
    Agree (2 ^ j)
      (newton (sqrtStep a (r * v)) (C ((1 + 1) * v)) (j + 1))
      (newton (sqrtStep a (r * v)) (C ((1 + 1) * v)) j) := by
  change Agree (2 ^ j)
    (sqrtStep a (r * v)
      (newton (sqrtStep a (r * v)) (C ((1 + 1) * v)) j)
      (2 ^ (j + 1)))
    (newton (sqrtStep a (r * v)) (C ((1 + 1) * v)) j)
  apply sqrtStep_stable a _ (r * v) (2 ^ j) (2 ^ (j + 1))
  · exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_succ j)
  · grind
  · exact sqrtNewton_correct a r v hr hv j

private theorem sqrtNewton_const [Lean.Grind.CommRing R]
    (a : TSeries R n) (r v : R) (hr : r * r = a.coeff 0)
    (hv : ((1 + 1) * r) * v = 1) (j : Nat) :
    Agree 1 (newton (sqrtStep a (r * v)) (C ((1 + 1) * v)) j)
      (C ((1 + 1) * v)) := by
  have hh : (1 + 1) * (r * v) = 1 := by grind
  induction j with
  | zero => exact Agree.refl 1 _
  | succ j ih =>
      change Agree 1
        (sqrtStep a (r * v)
          (newton (sqrtStep a (r * v)) (C ((1 + 1) * v)) j)
          (2 ^ (j + 1))) (C ((1 + 1) * v))
      exact (sqrtStep_stable a _ (r * v) 1 (2 ^ (j + 1)) (by
        have : 0 < 2 ^ (j + 1) := Nat.two_pow_pos _
        omega) hh ((sqrtNewton_correct a r v hr hv j).mono (by
          have : 0 < 2 ^ j := Nat.two_pow_pos _
          omega))).trans ih

private theorem sqrtOfRoot_eq [Lean.Grind.CommRing R]
    (a : TSeries R n) (r v : R) :
    sqrtOfRoot a r v =
      a * newton (sqrtStep a (r * v)) (C ((1 + 1) * v)) (steps n) := by
  apply ext
  intro i hi
  unfold sqrtOfRoot sqrtUpTo
  simp only [Nat.min_self]
  rw [coeff_ofFn _ i hi, if_pos hi, coeff_mulUpTo n _ _ i hi, if_pos hi]

/-- Bounded square-root lifting agrees with the full lift throughout the
requested prefix. -/
theorem sqrtUpTo_agree [Lean.Grind.CommRing R]
    (m : Nat) (a : TSeries R n) (r v : R)
    (hr : r * r = a.coeff 0) (hv : ((1 + 1) * r) * v = 1) :
    Agree m (sqrtUpTo m a r v) (sqrtOfRoot a r v) := by
  let q := min m n
  let init : TSeries R n := C ((1 + 1) * v)
  let short := newton (sqrtStep a (r * v)) init (steps q)
  let full := newton (sqrtStep a (r * v)) init (steps n)
  have hiter : Agree q short full := by
    have h := newton_agree (sqrtStep a (r * v)) init
      (sqrtNewton_stable a r v hr hv)
      (steps_mono (Nat.min_le_right m n))
    exact (h.mono (two_pow_steps_ge q)).symm
  have hmul : Agree q (mulUpTo m a short) (a * full) := by
    exact ((Agree.mulUpTo m a short).mono (Nat.min_le_left m n)).trans
      (Agree.mul (Agree.refl q a) hiter)
  intro i hi him
  have hiq : i < q := by dsimp only [q]; omega
  unfold sqrtUpTo
  rw [coeff_ofFn _ i hi, if_pos him]
  rw [sqrtOfRoot_eq]
  exact hmul i hi hiq

/-- Newton lifting squares to the input under the stated root and unit
hypotheses. -/
theorem sqrtOfRoot_sq [Lean.Grind.CommRing R] (a : TSeries R n) (r v : R)
    (hr : r * r = a.coeff 0) (hv : ((1 + 1) * r) * v = 1) :
    sqrtOfRoot a r v * sqrtOfRoot a r v = a := by
  let z := newton (sqrtStep a (r * v)) (C ((1 + 1) * v)) (steps n)
  have herr : sqrtError a z = 0 := by
    apply Agree.full (p := n)
    · exact (sqrtNewton_correct a r v hr hv (steps n)).mono
        (two_pow_steps_ge n)
    · omega
  have haz : a * z * z = 1 := by
    unfold sqrtError at herr
    grind
  rw [sqrtOfRoot_eq]
  change (a * z) * (a * z) = a
  grind

/-- The lifted square root retains the chosen constant root. -/
theorem sqrtOfRoot_coeff_zero [Lean.Grind.CommRing R]
    (a : TSeries R n) (r v : R) (hr : r * r = a.coeff 0)
    (hv : ((1 + 1) * r) * v = 1) (h : 0 < n) :
    (sqrtOfRoot a r v).coeff 0 = r := by
  let z := newton (sqrtStep a (r * v)) (C ((1 + 1) * v)) (steps n)
  rw [sqrtOfRoot_eq]
  change (a * z).coeff 0 = r
  rw [coeff_mul_zero a z h]
  have hz := sqrtNewton_const a r v hr hv (steps n) 0 h (by omega)
  rw [hz, coeff_C ((1 + 1) * v) 0 h]
  grind

/-- A square root is unique once its constant root has been fixed and `2*r`
is a unit. -/
theorem sqrt_unique [Lean.Grind.CommRing R] (s t : TSeries R n) (r v : R)
    (hv : ((1 + 1) * r) * v = 1) (hs : s * s = t * t)
    (hsr : s.coeff 0 = r) (htr : t.coeff 0 = r) : s = t := by
  by_cases hn : n = 0
  · apply ext
    intro _ hi
    omega
  · have hunit : (s + t).coeff 0 * v = 1 := by
      rw [coeff_add s t 0 (by omega), hsr, htr]
      grind
    have hfactor : (s - t) * (s + t) = 0 := by
      grind
    have hinv := invOfUnit_mul (s + t) v hunit
    have hzero : s - t = 0 := by
      calc
        s - t = (s - t) * 1 := (mul_one _).symm
        _ = (s - t) * ((s + t) * invOfUnit (s + t) v) := by rw [hinv]
        _ = ((s - t) * (s + t)) * invOfUnit (s + t) v :=
          (mul_assoc _ _ _).symm
        _ = 0 := by rw [hfactor, zero_mul]
    grind

/-- Optional square-root lifting has the precision-sensitive success
condition required by the zero and one coefficient cases. -/
theorem sqrt?_isSome_iff [Lean.Grind.CommRing R] [DecidableEq R]
    [UnitOps R] [LawfulUnitOps R] (a : TSeries R n) (r : R) :
    (sqrt? a r).isSome = true ↔
      n = 0 ∨ (r * r = a.coeff 0 ∧
        (n ≤ 1 ∨ ∃ v, ((1 + 1) * r) * v = 1)) := by
  by_cases hn0 : n = 0
  · simp [sqrt?, hn0]
  by_cases hr : r * r = a.coeff 0
  · by_cases hn1 : n ≤ 1
    · simp [sqrt?, hn0, hr, hn1]
    · rw [show sqrt? a r =
        match UnitOps.inv? (R := R) ((1 + 1) * r) with
        | some v => some (sqrtOfRoot a r v)
        | none => none by simp [sqrt?, hn0, hr, hn1]]
      cases hq : UnitOps.inv? (R := R) ((1 + 1) * r) with
      | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, false_iff, hn0,
            hr, true_and, hn1, false_or]
          intro hunit
          have hsome := LawfulUnitOps.inv?_isSome (R := R) ((1 + 1) * r) hunit
          simp [hq] at hsome
      | some v =>
          simp only [Option.isSome_some, hn0, hr, true_and, hn1, false_or, true_iff]
          exact ⟨v, LawfulUnitOps.inv?_eq (R := R) ((1 + 1) * r) v hq⟩
  · simp [sqrt?, hn0, hr]

end Hex.TSeries
