/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Basic
public import HexSignDetMathlib.SelectedRoot
public import HexSturmMathlib.Domain
public import HexRealRootsMathlib.RealClosed

public section

namespace Hex.RealClosure

open HexPolyMathlib.Interpret

private noncomputable instance : DecidableEq ℝ := Classical.decEq ℝ

private def ratCast : Rat → ℝ := fun q => (q : ℝ)
private theorem ratZero (q : Rat) : ratCast q = 0 ↔ q = 0 := Rat.cast_eq_zero
private theorem ratOne : ratCast (1 : Rat) = 1 := by simp [ratCast]
private theorem ratAdd (a b : Rat) : ratCast (a + b) = ratCast a + ratCast b := by
  simp [ratCast]
private theorem ratSub (a b : Rat) : ratCast (a - b) = ratCast a - ratCast b := by
  simp [ratCast]
private theorem ratMul (a b : Rat) : ratCast (a * b) = ratCast a * ratCast b := by
  simp [ratCast]
private theorem ratNat (n : Nat) : ratCast (n : Rat) = (n : ℝ) := by
  simp [ratCast]

private theorem ratSign (q : Rat) :
    Sturm.orderSign q = (SignType.sign (ratCast q) : Int) := by
  by_cases hn : q < 0
  · have hn' : ratCast q < 0 := by simpa [ratCast] using hn
    simp [Sturm.orderSign, hn, sign_eq_neg_one_iff.mpr hn']
  · by_cases hz : q = 0
    · subst q
      simp [Sturm.orderSign, ratCast]
    · have hp : 0 < q := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
      have hp' : 0 < ratCast q := by simpa [ratCast] using hp
      simp [Sturm.orderSign, hn, hz, sign_eq_one_iff.mpr hp']

/-- The real root denoted by a checked rational descriptor. -/
noncomputable def Root.real {context : Nat} (d : Root context) : ℝ :=
  d.root ratCast ratZero ratOne ratAdd ratSub ratMul ratNat ratSign

namespace Expression

/-- Evaluate the stored polynomial at the descriptor's selected real root. -/
noncomputable def denote {context : Nat} {d : Root context} (a : Expression d) : ℝ :=
  (interpret ratCast ratZero a.polynomial).eval d.real

@[simp] theorem denote_zero {context : Nat} {d : Root context} :
    (zero (d := d)).denote = 0 := by
  simp [denote, zero]

@[simp] theorem denote_one {context : Nat} {d : Root context} :
    (one (d := d)).denote = 1 := by
  simp [denote, one, interpret_one ratCast ratZero ratOne]

@[simp] theorem denote_add {context : Nat} {d : Root context} (a b : Expression d) :
    (add a b).denote = a.denote + b.denote := by
  simp [denote, add, interpret_add ratCast ratZero ratAdd]

@[simp] theorem denote_neg {context : Nat} {d : Root context} (a : Expression d) :
    (neg a).denote = -a.denote := by
  simp [denote, neg, interpret_neg ratCast ratZero ratSub]

@[simp] theorem denote_sub {context : Nat} {d : Root context} (a b : Expression d) :
    (sub a b).denote = a.denote - b.denote := by
  simp [denote, sub, interpret_sub ratCast ratZero ratSub]

@[simp] theorem denote_mul {context : Nat} {d : Root context} (a b : Expression d) :
    (mul a b).denote = a.denote * b.denote := by
  simp [denote, mul, interpret_mul ratCast ratZero ratAdd ratMul]

/-- Accepted one-query evidence computes the sign of the selected real value. -/
theorem sign?_sound {context : Nat} {d : Root context} (a : Expression d) (value : Int)
    (h : a.sign? = .ok value) :
    value = (SignType.sign a.denote : Int) := by
  unfold sign? at h
  cases hs : d.buildSigns [a.polynomial] with
  | error err => simp [hs] at h
  | ok s =>
    have heq : s.value = value := by simpa [hs] using h
    simpa [denote, Root.real, heq] using
      (s.value_at_root ratCast ratZero ratOne ratAdd ratSub ratMul ratNat ratSign)

/-- A checked zero sign reflects zero at the selected real root. -/
theorem sign?_zero {context : Nat} {d : Root context} (a : Expression d)
    (h : a.sign? = .ok 0) : a.denote = 0 := by
  have hs := a.sign?_sound 0 h
  have hs0 : (SignType.sign a.denote : Int) = 0 := hs.symm
  have hs0' : SignType.sign a.denote = 0 := by
    cases hsg : SignType.sign a.denote <;> simp [hsg] at hs0 ⊢
  exact sign_eq_zero_iff.mp hs0'

/-- The checked inverse result is an inverse of the value at the selected root. -/
theorem inverse?_sound {context : Nat} {d : Root context} (a b : Expression d)
    (h : a.inverse? = .ok (some b)) : a.denote * b.denote = 1 := by
  cases hs : a.sign? with
  | error err => simp [inverse?, hs] at h
  | ok sa =>
    by_cases hz : sa = 0
    · simp [inverse?, hs, hz] at h
    · cases hc : (sub (mul a a.inverseCandidate) one).sign? with
      | error err => simp [inverse?, hs, hz, hc] at h
      | ok sc =>
        by_cases hsc : sc = 0
        · have hb : a.inverseCandidate = b := by
            simpa [inverse?, hs, hz, hc, hsc] using h
          subst b
          have hzero : (sub (mul a a.inverseCandidate) one).denote = 0 :=
            sign?_zero _ (by simpa [hsc] using hc)
          have hprod : a.denote * a.inverseCandidate.denote - 1 = 0 := by
            simpa using hzero
          exact sub_eq_zero.mp hprod
        · simp [inverse?, hs, hz, hc, hsc] at h

/-- Checked re-encoding changes the defining polynomial without changing the
real value of an expression. -/
theorem denote_transport {context : Nat} {d : Root context} {head : DensePoly Rat}
    {lower upper : Endpoint Rat} (r : SignDet.Reencoding d head lower upper)
    (a : Expression d) : (transport r a).denote = a.denote := by
  have hroot := r.root_eq_source ratCast ratZero ratOne ratAdd ratSub ratMul ratNat ratSign
  simpa [denote, transport, Root.real] using
    congrArg (fun x : ℝ => (interpret ratCast ratZero a.polynomial).eval x) hroot

end Expression
end Hex.RealClosure

/- The inherited `sorryAx` is `HexRealRootsMathlib.Tarski.check_rootSum` (#10389). -/
/-- info: 'Hex.RealClosure.Expression.inverse?_sound' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Expression.inverse?_sound
/-- info: 'Hex.RealClosure.Expression.denote_transport' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Expression.denote_transport
