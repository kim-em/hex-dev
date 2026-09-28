/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ZeroFactor
public import HexPolyMathlib.Interpret
public import Mathlib.Algebra.Polynomial.RingDivision

public section

namespace Hex.RealClosure.ZeroFactor
open HexPolyMathlib.Interpret

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [Field K] [DecidableEq K]
variable (φ : E → K) (hz : ∀ a, φ a = 0 ↔ a = 0)

/-- Literal zero reflection makes the executed scan the polynomial's exact
trailing degree, even when distinct nonzero representations denote one value. -/
theorem order_eq (p : DensePoly E) :
    order p = (interpret φ hz p).natTrailingDegree := by
  by_cases hp : p = 0
  · subst p
    simp [order, show (0 : DensePoly E).coeffs = #[] from rfl]
  have hp' : interpret φ hz p ≠ 0 := fun h => hp ((interpret_eq_zero φ hz p).mp h)
  have hn := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp'
  rw [coeff_interpret] at hn
  have hb : (interpret φ hz p).natTrailingDegree < p.coeffs.size := by
    by_contra h
    have zero := DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt h)
    exact hn (zero ▸ (hz 0).mpr rfl)
  apply (Array.findIdx_eq hb).mpr
  constructor
  · have ne : p.coeff (interpret φ hz p).natTrailingDegree ≠ 0 :=
      fun h => hn (h ▸ (hz 0).mpr rfl)
    simpa only [bne_iff_ne, DensePoly.coeff, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hb, Option.getD_some] using ne
  · intro j hj
    have zero := Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj
    rw [coeff_interpret] at zero
    have stored := (hz _).mp zero
    simpa only [bne_eq_false_iff_eq, DensePoly.coeff, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (hj.trans hb), Option.getD_some] using stored

/-- The actual sliced quotient gives exact factorization, including zero. -/
theorem remove_factor (p : DensePoly E) :
    interpret φ hz p = Polynomial.X ^ (remove p).2 * interpret φ hz (remove p).1 := by
  have h0 : φ 0 = 0 := (hz 0).mpr rfl
  ext i
  rw [Polynomial.coeff_X_pow_mul', coeff_interpret]
  change φ (p.coeff i) =
    if order p ≤ i then (interpret φ hz (remove p).1).coeff (i - order p) else 0
  split
  · rename_i hi
    rw [coeff_interpret, remove_coeff, Nat.add_sub_of_le hi]
  · rename_i hi
    rw [coeff_zero p i (Nat.lt_of_not_ge hi), h0]

/-- The actual returned quotient is nonzero and root-free at zero. Its exact
factorization preserves the input scalar and accounts for the degree drop. -/
theorem remove_spec (p : DensePoly E) (hp : interpret φ hz p ≠ 0) :
    interpret φ hz (remove p).1 ≠ 0 ∧
    (interpret φ hz (remove p).1).eval 0 ≠ 0 ∧
    interpret φ hz p = Polynomial.X ^ (remove p).2 * interpret φ hz (remove p).1 ∧
    p.natDegree = (remove p).1.natDegree + (remove p).2 := by
  have nonroot : (interpret φ hz (remove p).1).eval 0 ≠ 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, coeff_interpret, remove_coeff, Nat.add_zero, order_eq φ hz]
    simpa only [coeff_interpret] using Polynomial.coeff_natTrailingDegree_ne_zero.mpr hp
  have nonzero : interpret φ hz (remove p).1 ≠ 0 := by
    intro h
    exact nonroot (by rw [h]; simp)
  have factor := remove_factor φ hz p
  have degree := congrArg Polynomial.natDegree factor
  rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) nonzero,
    Polynomial.natDegree_X_pow, natDegree_interpret, natDegree_interpret] at degree
  exact ⟨nonzero, nonroot, factor, by omega⟩

/-- The extracted exponent is the input's exact zero-root multiplicity. -/
theorem remove_multiplicity (p : DensePoly E) (hp : interpret φ hz p ≠ 0) :
    (interpret φ hz p).rootMultiplicity 0 = (remove p).2 := by
  obtain ⟨nonzero, nonroot, factor, _⟩ := remove_spec φ hz p hp
  have hn : ¬ (interpret φ hz (remove p).1).IsRoot 0 := nonroot
  have hmultiplicity := Polynomial.rootMultiplicity_mul_X_sub_C_pow
    (a := (0 : K)) (n := (remove p).2) nonzero
  rw [factor, mul_comm]
  simpa only [Polynomial.C_0, sub_zero, Polynomial.rootMultiplicity_eq_zero hn,
    zero_add] using hmultiplicity

/-- Extracting zero roots preserves the original leading scalar. -/
theorem remove_leadingCoeff (p : DensePoly E) (hp : interpret φ hz p ≠ 0) :
    φ p.leadingCoeff = φ (remove p).1.leadingCoeff := by
  obtain ⟨_, _, factor, _⟩ := remove_spec φ hz p hp
  have hc := congrArg Polynomial.leadingCoeff factor
  simpa only [leadingCoeff_interpret, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_pow, Polynomial.leadingCoeff_X, one_pow, one_mul] using hc

/-- Every nonzero root remains a root of the actual returned quotient. -/
theorem remove_roots (p : DensePoly E) (hp : interpret φ hz p ≠ 0)
    (x : K) (hx : x ≠ 0) :
    (interpret φ hz p).IsRoot x ↔ (interpret φ hz (remove p).1).IsRoot x := by
  obtain ⟨_, _, factor, _⟩ := remove_spec φ hz p hp
  rw [factor]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, mul_eq_zero, pow_eq_zero_iff', hx, false_and, false_or]

/-- Zero extraction retains the exact multiplicity of every nonzero root. -/
theorem remove_rootMultiplicity (p : DensePoly E) (hp : interpret φ hz p ≠ 0)
    (x : K) (hx : x ≠ 0) :
    (interpret φ hz p).rootMultiplicity x =
      (interpret φ hz (remove p).1).rootMultiplicity x := by
  have factor := remove_factor φ hz p
  have hproduct : Polynomial.X ^ (remove p).2 * interpret φ hz (remove p).1 ≠ 0 :=
    factor ▸ hp
  have nonroot : ¬ (Polynomial.X ^ (remove p).2 : Polynomial K).IsRoot x := by
    simp only [Polynomial.IsRoot.def, Polynomial.eval_pow, Polynomial.eval_X]
    exact pow_ne_zero _ hx
  rw [factor, Polynomial.rootMultiplicity_mul hproduct,
    Polynomial.rootMultiplicity_eq_zero nonroot, zero_add]

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

/-- info: 'Hex.RealClosure.ZeroFactor.remove_rootMultiplicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.ZeroFactor.remove_rootMultiplicity
