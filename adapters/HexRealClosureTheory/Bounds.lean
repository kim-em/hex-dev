/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Bounds
public import HexPolyTheory.Interpret
public import HexSturmTheory.Domain
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Basic.Sign.Basic

public section

namespace Hex.RealClosure.Bounds

open Finset

/-- The strict coefficient bound excludes every root outside `(-B, B)` over
any ordered field; no Archimedean or normed-field hypothesis is used. -/
theorem root_abs_lt {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : Polynomial K) (hp : p ≠ 0) (bound : K)
    (hc : ∀ i < p.natDegree, |p.coeff i| < (bound - 1) * |p.leadingCoeff|)
    (x : K) (hx : p.IsRoot x) : |x| < bound := by
  by_contra h
  have hbx : bound ≤ |x| := le_of_not_gt h
  have hlc : 0 < |p.leadingCoeff| := abs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp)
  have hs : 0 ≤ ∑ i ∈ range p.natDegree, |x| ^ i :=
    sum_nonneg fun i _ => pow_nonneg (abs_nonneg x) i
  have he := hx
  rw [Polynomial.IsRoot.def, Polynomial.eval_eq_sum_range, sum_range_succ] at he
  rw [Polynomial.coeff_natDegree, add_eq_zero_iff_eq_neg] at he
  have ha := congrArg (fun a : K => |a|) he
  rw [abs_neg, abs_mul, abs_pow] at ha
  have hsum : |p.leadingCoeff| * |x| ^ p.natDegree ≤
      |p.leadingCoeff| * (bound - 1) * ∑ i ∈ range p.natDegree, |x| ^ i := by
    calc
      |p.leadingCoeff| * |x| ^ p.natDegree =
          |∑ i ∈ range p.natDegree, p.coeff i * x ^ i| := ha.symm
      _ ≤ ∑ i ∈ range p.natDegree, |p.coeff i * x ^ i| := abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ range p.natDegree, |p.coeff i| * |x| ^ i := by
        simp only [abs_mul, abs_pow]
      _ ≤ ∑ i ∈ range p.natDegree,
          (bound - 1) * |p.leadingCoeff| * |x| ^ i := by
        apply sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (hc i (mem_range.mp hi)).le
          (pow_nonneg (abs_nonneg x) i)
      _ = |p.leadingCoeff| * (bound - 1) *
          ∑ i ∈ range p.natDegree, |x| ^ i := by rw [← mul_sum]; ring
  have hcompare : (bound - 1) * (∑ i ∈ range p.natDegree, |x| ^ i) ≤
      (|x| - 1) * (∑ i ∈ range p.natDegree, |x| ^ i) :=
    mul_le_mul_of_nonneg_right (sub_le_sub_right hbx 1) hs
  have hgeom := mul_geom_sum |x| p.natDegree
  have hfinal : |p.leadingCoeff| * |x| ^ p.natDegree ≤
      |p.leadingCoeff| * (|x| ^ p.natDegree - 1) := by
    calc
      _ ≤ |p.leadingCoeff| * ((bound - 1) *
          ∑ i ∈ range p.natDegree, |x| ^ i) := by simpa only [mul_assoc] using hsum
      _ ≤ |p.leadingCoeff| * ((|x| - 1) *
          ∑ i ∈ range p.natDegree, |x| ^ i) :=
        mul_le_mul_of_nonneg_left hcompare hlc.le
      _ = _ := by rw [hgeom]
  nlinarith

private theorem cast_sign_pos {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (x : K) :
    0 < (SignType.sign x : Int) ↔ 0 < x := by
  rcases lt_trichotomy x 0 with h | h | h
  · simp [_root_.sign_neg h, not_lt_of_ge h.le]
  · simp [h]
  · simp [_root_.sign_pos h, h]

/-- Natural-cast preservation interprets the actual finite candidates as
dyadic powers in the semantic coefficient field. -/
theorem find?_dyadic {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
    [One E] [Neg E] [Sub E] [Mul E] [NatCast E] [Semiring K]
    (φ : E → K) (hnat : ∀ n : Nat, φ (n : E) = (n : K))
    {sign : E → Int} {p : DensePoly E} {bound : Bound sign p}
    (h : find? sign p = some bound) :
    ∃ exponent, 1 ≤ exponent ∧ exponent ≤ 2 * (p.natDegree + 1) ∧
      φ bound.value = (2 : K) ^ exponent := by
  obtain ⟨exponent, hpos, hle, hv⟩ := find?_exponent h
  refine ⟨exponent, hpos, hle, ?_⟩
  rw [hv, hnat]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

/-- The executable absolute value denotes the ordered-field absolute value. -/
theorem abs_map {E : Type u} {K : Type v} [Neg E]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (φ : E → K) (hn : ∀ a, φ (-a) = -φ a)
    (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (φ a) : Int))
    (a : E) : φ (abs sign a) = |φ a| := by
  unfold abs
  rw [hsign a]
  rcases lt_trichotomy (φ a) 0 with h | h | h
  · simp [_root_.sign_neg h, hn, abs_of_neg h]
  · simp [h]
  · simp [_root_.sign_pos h, abs_of_pos h]

section Interpretation

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E] [One E]
variable [Neg E] [Sub E] [Mul E]
variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [DecidableEq K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (hn : ∀ a, φ (-a) = -φ a)
variable (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)
variable (sign : E → Int) (hsign : ∀ a, sign a = (SignType.sign (φ a) : Int))

include h1 hn hs hm hsign in
/-- Every accepted bound contains all roots strictly, including over a
non-Archimedean ambient field and noninjective coefficient representations. -/
theorem check_sound (p : DensePoly E) (bound : E)
    (checked : check sign p bound = true) :
    1 < φ bound ∧ ∀ x : K,
      (HexPolyTheory.Interpret.interpret φ hz p).IsRoot x → |x| < φ bound := by
  have hp : p ≠ 0 := check_nonzero checked
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at checked
  have hb := (cast_sign_pos (φ (bound - 1))).mp
    (by simpa only [hsign] using checked.1.2)
  rw [hs, h1] at hb
  refine ⟨by linarith, ?_⟩
  intro x hx
  apply root_abs_lt (HexPolyTheory.Interpret.interpret φ hz p)
    (fun h => hp ((HexPolyTheory.Interpret.interpret_eq_zero φ hz p).mp h))
    (φ bound) ?_ x hx
  intro i hi
  rw [HexPolyTheory.Interpret.natDegree_interpret] at hi
  have hc : 0 < sign ((bound - 1) * abs sign p.leadingCoeff - abs sign (p.coeff i)) :=
    of_decide_eq_true (List.all_eq_true.mp checked.2 i (List.mem_range.mpr hi))
  rw [hsign] at hc
  have hc' := (cast_sign_pos _).mp hc
  rw [hs, hm, hs, h1, abs_map φ hn sign hsign, abs_map φ hn sign hsign] at hc'
  simpa only [HexPolyTheory.Interpret.coeff_interpret,
    HexPolyTheory.Interpret.leadingCoeff_interpret] using (sub_pos.mp hc')

include h1 hn hs hm hsign in
/-- Checked bound values are strict open endpoints for the entire root set. -/
theorem Bound.roots (p : DensePoly E) (bound : Bound sign p) :
    1 < φ bound.value ∧ ∀ x : K,
      (HexPolyTheory.Interpret.interpret φ hz p).IsRoot x →
        -φ bound.value < x ∧ x < φ bound.value := by
  obtain ⟨hb, hr⟩ := check_sound φ hz h1 hn hs hm sign hsign p bound.value bound.accepted
  exact ⟨hb, fun x hx => abs_lt.mp (hr x hx)⟩

include h1 hn hs hm hsign in
/-- A checked bound supplies ordered root-free endpoints for the shared
Sturm domain. Squarefreeness is supplied by the decomposition theorem. -/
theorem Bound.domain (p : DensePoly E) (bound : Bound sign p)
    (hfree : Squarefree (HexPolyTheory.Interpret.interpret φ hz p)) :
    HexSturmTheory.Domain φ hz p (.finite (-bound.value)) (.finite bound.value) := by
  obtain ⟨hb, hr⟩ := bound.roots φ hz h1 hn hs hm sign hsign p
  refine ⟨?_, hfree, ?_, ?_, ?_⟩
  · exact fun h => check_nonzero bound.accepted
      ((HexPolyTheory.Interpret.interpret_eq_zero φ hz p).mp h)
  · change φ (-bound.value) < φ bound.value
    rw [hn]
    linarith
  · change (HexPolyTheory.Interpret.interpret φ hz p).eval (φ (-bound.value)) ≠ 0
    rw [hn]
    intro h
    exact (lt_irrefl _) (hr (-φ bound.value) h).1
  · change (HexPolyTheory.Interpret.interpret φ hz p).eval (φ bound.value) ≠ 0
    intro h
    exact (lt_irrefl _) (hr (φ bound.value) h).2

end Interpretation

end Hex.RealClosure.Bounds

/-- info: 'Hex.RealClosure.Bounds.root_abs_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Bounds.root_abs_lt

/-- info: 'Hex.RealClosure.Bounds.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Bounds.check_sound

/-- info: 'Hex.RealClosure.Bounds.Bound.roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Bounds.Bound.roots

/-- info: 'Hex.RealClosure.Bounds.find?_dyadic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Bounds.find?_dyadic

/-- info: 'Hex.RealClosure.Bounds.Bound.domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Bounds.Bound.domain
