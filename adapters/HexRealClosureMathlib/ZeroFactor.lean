/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ZeroFactor
public import HexRealClosureMathlib.Deflation
public import Mathlib.Algebra.Polynomial.RingDivision

public section

namespace Hex.RealClosure.ZeroFactor
open HexPolyMathlib.Interpret

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Sub E] [Mul E] [Field K] [DecidableEq K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)
variable (h1 : φ 1 = 1) (hs : ∀ a b, φ (a - b) = φ a - φ b)
variable (hm : ∀ a b, φ (a * b) = φ a * φ b)

include hz h1 hs hm in
/-- Degree fuel exhausts every factor of `X`. The actual returned quotient is
nonzero and root-free at zero, and the exact product keeps the input scalar. -/
theorem extract_spec (p : DensePoly E) (fuel : Nat)
    (hp : interpret φ hz p ≠ 0) (bound : p.natDegree ≤ fuel) :
    interpret φ hz (extract p fuel).1 ≠ 0 ∧
    (interpret φ hz (extract p fuel).1).eval 0 ≠ 0 ∧
    interpret φ hz p = Polynomial.X ^ (extract p fuel).2 *
      interpret φ hz (extract p fuel).1 ∧
    p.natDegree = (extract p fuel).1.natDegree + (extract p fuel).2 := by
  have h0 : φ 0 = 0 := (hz 0).mpr rfl
  induction fuel generalizing p with
  | zero =>
    have hn : (interpret φ hz p).eval 0 ≠ 0 := by
      intro hr
      have hd := (deflate?_success φ hz h1 hs hm p 0).mpr ⟨hp, by
        simpa only [Polynomial.IsRoot.def, h0] using hr⟩
      cases hc : deflate? p 0 with
      | none => simp [hc] at hd
      | some d => have := d.degree φ hz h1 hs hm; omega
    simp only [extract, pow_zero, one_mul, Nat.add_zero]
    exact ⟨hp, hn, trivial, trivial⟩
  | succ fuel ih =>
    cases hd : deflate? p 0 with
    | none =>
      have hn : (interpret φ hz p).eval 0 ≠ 0 := by
        intro hr
        have accepted := (deflate?_success φ hz h1 hs hm p 0).mpr ⟨hp, by
          simpa only [Polynomial.IsRoot.def, h0] using hr⟩
        simp [hd] at accepted
      simp only [extract, hd, pow_zero, one_mul, Nat.add_zero]
      exact ⟨hp, hn, trivial, trivial⟩
    | some d =>
      have degree := d.degree φ hz h1 hs hm
      obtain ⟨nonzero, nonroot, factor, remaining⟩ :=
        ih d.quotient (d.quotient_nonzero φ hz h1 hs hm) (by omega)
      simp only [extract, hd]
      refine ⟨nonzero, nonroot, ?_, by omega⟩
      rw [d.factor φ hz h1 hs hm, h0, Polynomial.C_0, sub_zero, factor,
        pow_succ', mul_assoc]

include hz h1 hs hm in
/-- The actual degree-bounded entry has an exact factorization and no zero
root left in its returned polynomial. -/
theorem remove_spec (p : DensePoly E) (hp : interpret φ hz p ≠ 0) :
    interpret φ hz (remove p).1 ≠ 0 ∧
    (interpret φ hz (remove p).1).eval 0 ≠ 0 ∧
    interpret φ hz p = Polynomial.X ^ (remove p).2 * interpret φ hz (remove p).1 ∧
    p.natDegree = (remove p).1.natDegree + (remove p).2 :=
  extract_spec φ hz h1 hs hm p p.natDegree hp (le_refl _)

include hz h1 hs hm in
/-- The extracted exponent is the input's exact zero-root multiplicity. -/
theorem remove_multiplicity (p : DensePoly E) (hp : interpret φ hz p ≠ 0) :
    (interpret φ hz p).rootMultiplicity 0 = (remove p).2 := by
  obtain ⟨nonzero, nonroot, factor, _⟩ := remove_spec φ hz h1 hs hm p hp
  have hn : ¬ (interpret φ hz (remove p).1).IsRoot 0 := nonroot
  have hmultiplicity := Polynomial.rootMultiplicity_mul_X_sub_C_pow
    (a := (0 : K)) (n := (remove p).2) nonzero
  rw [factor, mul_comm]
  simpa only [Polynomial.C_0, sub_zero, Polynomial.rootMultiplicity_eq_zero hn,
    zero_add] using hmultiplicity

include hz h1 hs hm in
/-- Extracting zero roots preserves the original leading scalar. -/
theorem remove_leadingCoeff (p : DensePoly E) (hp : interpret φ hz p ≠ 0) :
    φ p.leadingCoeff = φ (remove p).1.leadingCoeff := by
  obtain ⟨_, _, factor, _⟩ := remove_spec φ hz h1 hs hm p hp
  have hc := congrArg Polynomial.leadingCoeff factor
  simpa only [leadingCoeff_interpret, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_X, one_pow, one_mul] using hc

include hz h1 hs hm in
/-- Every nonzero root remains a root of the actual returned head. -/
theorem remove_roots (p : DensePoly E) (hp : interpret φ hz p ≠ 0)
    (x : K) (hx : x ≠ 0) :
    (interpret φ hz p).IsRoot x ↔ (interpret φ hz (remove p).1).IsRoot x := by
  obtain ⟨_, _, factor, _⟩ := remove_spec φ hz h1 hs hm p hp
  rw [factor]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, mul_eq_zero, pow_eq_zero_iff', hx, false_and, false_or]

end Hex.RealClosure.ZeroFactor

/-- info: 'Hex.RealClosure.ZeroFactor.remove_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.ZeroFactor.remove_spec

/-- info: 'Hex.RealClosure.ZeroFactor.remove_multiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.ZeroFactor.remove_multiplicity

/-- info: 'Hex.RealClosure.ZeroFactor.remove_leadingCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.ZeroFactor.remove_leadingCoeff

/-- info: 'Hex.RealClosure.ZeroFactor.remove_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.ZeroFactor.remove_roots
