/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.Deflation
public import HexPolyMathlib.Interpret
public import HexSturmMathlib.Domain
public import Mathlib.Algebra.Squarefree.Basic

public section

namespace Hex.RealClosure

open HexPolyMathlib.Interpret

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [Div E]
variable [Field K] [DecidableEq K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)
variable (hd : ∀ a b, φ (a / b) = φ a / φ b)

include h1 hs in
omit [Add E] [Mul E] [Div E] in
/-- The executable linear factor has the intended root, even for noninjective
coefficient representations. -/
theorem linear_map (root : E) :
    interpret φ hz (linear root) = Polynomial.X - Polynomial.C (φ root) := by
  rw [linear, interpret_sub φ hz hs, interpret_C]
  congr 1
  ext i
  rcases i with _ | (_ | i) <;>
    simp [coeff_interpret, DensePoly.coeff_ofCoeffs, Array.getD, (hz 0).mpr rfl, h1]
  simp [Polynomial.coeff_X, (hz (Zero.zero : E)).mpr rfl]

include h1 hs hm hd in
/-- Exact deflation succeeds precisely on a root of a nonzero input. -/
theorem deflate?_success (p : DensePoly E) (root : E) :
    (deflate? p root).isSome = true ↔
      interpret φ hz p ≠ 0 ∧ (interpret φ hz p).IsRoot (φ root) := by
  rw [deflate?_isSome]
  apply and_congr (not_congr (interpret_eq_zero φ hz p).symm)
  have hr := interpret_eq_zero φ hz (DensePoly.divMod p (linear root)).2
  rw [interpret_rem φ hz hs hm hd, linear_map φ hz h1 hs,
    Polynomial.mod_X_sub_C_eq_C_eval, Polynomial.C_eq_zero] at hr
  exact hr.symm

include h1 hs hm hd in
/-- The stored quotient gives exact factorization, with no monicization of
the original polynomial or scalar loss. -/
theorem Deflation.factor {p : DensePoly E} {root : E} (d : Deflation p root) :
    interpret φ hz p =
      (Polynomial.X - Polynomial.C (φ root)) * interpret φ hz d.quotient := by
  have h := interpret_divMod φ hz hs hm hd p (linear root)
  rw [d.divided] at h
  have hq := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  dsimp only at hq hr
  rw [linear_map φ hz h1 hs] at hq hr
  have he := EuclideanDomain.div_add_mod (interpret φ hz p)
    (Polynomial.X - Polynomial.C (φ root))
  rw [← hq, ← hr, interpret_zero, add_zero] at he
  exact he.symm

include h1 hs hm hd in
/-- Removing one root never turns a nonzero input into the zero polynomial. -/
theorem Deflation.quotient_nonzero {p : DensePoly E} {root : E}
    (d : Deflation p root) : interpret φ hz d.quotient ≠ 0 := by
  intro h
  have hf := d.factor φ hz h1 hs hm hd
  rw [h, mul_zero] at hf
  exact d.nonzero ((interpret_eq_zero φ hz p).mp hf)

include hz h1 hs hm hd in
/-- Exact removal reduces the degree by one, including the linear input case. -/
theorem Deflation.degree {p : DensePoly E} {root : E} (d : Deflation p root) :
    p.natDegree = d.quotient.natDegree + 1 := by
  have hf := d.factor φ hz h1 hs hm hd
  have hq := d.quotient_nonzero φ hz h1 hs hm hd
  have hn := congrArg Polynomial.natDegree hf
  rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hq,
    Polynomial.natDegree_X_sub_C] at hn
  simpa only [natDegree_interpret, Nat.add_comm] using hn

include h1 hs hm hd in
/-- The original root set is the removed point together with the quotient's
roots. This statement does not assume squarefreeness. -/
theorem Deflation.roots {p : DensePoly E} {root : E} (d : Deflation p root) (x : K) :
    (interpret φ hz p).IsRoot x ↔
      x = φ root ∨ (interpret φ hz d.quotient).IsRoot x := by
  rw [d.factor φ hz h1 hs hm hd, Polynomial.root_mul]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_eq_zero]

include h1 hs hm hd in
/-- A factor of a squarefree input is squarefree. -/
theorem Deflation.squarefree {p : DensePoly E} {root : E} (d : Deflation p root)
    (hfree : Squarefree (interpret φ hz p)) :
    Squarefree (interpret φ hz d.quotient) := by
  apply hfree.squarefree_of_dvd
  exact ⟨Polynomial.X - Polynomial.C (φ root),
    by rw [d.factor φ hz h1 hs hm hd, mul_comm]⟩

include h1 hs hm hd in
/-- Squarefreeness makes the removed point a valid open endpoint for the
quotient. Removing a root of a repeated factor would not have this property. -/
theorem Deflation.root_free {p : DensePoly E} {root : E} (d : Deflation p root)
    (hfree : Squarefree (interpret φ hz p)) :
    (interpret φ hz d.quotient).eval (φ root) ≠ 0 := by
  rw [d.factor φ hz h1 hs hm hd] at hfree
  intro hr
  have hunit := (IsRelPrime.of_squarefree_mul hfree).isUnit_of_dvd
    (Polynomial.dvd_iff_isRoot.mpr hr)
  exact Polynomial.not_isUnit_X_sub_C (φ root) hunit

include h1 hs hm hd in
/-- Existing root-free endpoints remain root-free after exact deflation. -/
theorem Deflation.nonvanishing
    {p : DensePoly E} {root : E} (d : Deflation p root) (endpoint : Endpoint E)
    (h : HexSturmMathlib.Nonvanishing φ (interpret φ hz p) endpoint) :
    HexSturmMathlib.Nonvanishing φ (interpret φ hz d.quotient) endpoint := by
  cases endpoint with
  | negInf => trivial
  | posInf => trivial
  | finite a =>
    change (interpret φ hz d.quotient).eval (φ a) ≠ 0
    intro hx
    have he := congrArg (fun f : Polynomial K => f.eval (φ a))
      (d.factor φ hz h1 hs hm hd)
    simp only [Polynomial.eval_mul, hx, mul_zero] at he
    exact h he

include h1 hs hm hd in
/-- A root encountered during bisection can become the shared open endpoint
of two new Sturm domains only after exact deflation of the squarefree head.
The old count certificates are not reused by this theorem. -/
theorem Deflation.domains [LinearOrder K] [IsStrictOrderedRing K]
    {p : DensePoly E} {root : E} (d : Deflation p root) (lower upper : Endpoint E)
    (domain : HexSturmMathlib.Domain φ hz p lower upper)
    (hl : HexSturmMathlib.EndpointLt φ lower (.finite root))
    (hu : HexSturmMathlib.EndpointLt φ (.finite root) upper) :
    HexSturmMathlib.Domain φ hz d.quotient lower (.finite root) ∧
      HexSturmMathlib.Domain φ hz d.quotient (.finite root) upper := by
  have hn := d.quotient_nonzero φ hz h1 hs hm hd
  have hf := d.squarefree φ hz h1 hs hm hd domain.2.1
  have hr := d.root_free φ hz h1 hs hm hd domain.2.1
  have ha := d.nonvanishing φ hz h1 hs hm hd lower domain.2.2.2.1
  have hb := d.nonvanishing φ hz h1 hs hm hd upper domain.2.2.2.2
  exact ⟨⟨hn, hf, hl, ha, hr⟩, ⟨hn, hf, hu, hr, hb⟩⟩

end Hex.RealClosure

/-- info: 'Hex.RealClosure.deflate?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.deflate?_success

/-- info: 'Hex.RealClosure.Deflation.factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Deflation.factor

/-- info: 'Hex.RealClosure.Deflation.degree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Deflation.degree

/-- info: 'Hex.RealClosure.Deflation.root_free' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Deflation.root_free

/-- info: 'Hex.RealClosure.Deflation.domains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Deflation.domains
