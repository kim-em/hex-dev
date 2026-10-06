/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteTowerUse
public import HexRealClosureMathlib.AlgebraicTower
public import HexSturmMathlib.Soundness
public import Mathlib.Analysis.Real.Sqrt

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal

open HexPolyMathlib.Interpret HexRealRootsMathlib Hex.SignDet

private noncomputable def cast (a : Rat) : ℝ := a
private theorem cast_zero (a : Rat) : cast a = 0 ↔ a = 0 := Rat.cast_eq_zero
private theorem cast_one : cast 1 = 1 := Rat.cast_one
private theorem cast_add (a b : Rat) : cast (a + b) = cast a + cast b := Rat.cast_add a b
private theorem cast_sub (a b : Rat) : cast (a - b) = cast a - cast b := Rat.cast_sub a b
private theorem cast_mul (a b : Rat) : cast (a * b) = cast a * cast b := Rat.cast_mul a b
private theorem cast_nat (n : Nat) : cast n = (n : ℝ) := by simp [cast]
private theorem cast_neg (a : Rat) : cast (-a) = -cast a := Rat.cast_neg a
private theorem cast_inv (a : Rat) : cast a⁻¹ = (cast a)⁻¹ := Rat.cast_inv a
private theorem cast_sign (a : Rat) : Sturm.orderSign a = (SignType.sign (cast a) : Int) := by
  rw [HexSturmMathlib.orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono a).symm

/-- The ordinary real root selected by the retained first descriptor. -/
noncomputable def alpha : ℝ := FiniteTower.first.rootValue
  cast cast_zero cast_one cast_add cast_sub cast_mul cast_nat cast_sign

/-- Interpret the actual first algebraic carrier in the ordinary reals.
This fixture has a rational predecessor and no infinitesimal stage. -/
noncomputable def read (a : Element FiniteTower.first) : ℝ := a.denote
  cast cast_zero cast_one cast_add cast_sub cast_mul cast_nat cast_sign

theorem read_zero (a : Element FiniteTower.first) : read a = 0 ↔ a = 0 :=
  a.denote_eq_zero cast cast_zero cast_one cast_add cast_sub cast_mul cast_nat cast_sign cast_neg cast_inv
private theorem read_one : read 1 = 1 :=
  Element.denote_one cast cast_zero cast_one cast_add cast_sub cast_mul cast_nat cast_sign cast_neg cast_inv
private theorem read_add (a b : Element FiniteTower.first) : read (a + b) = read a + read b :=
  Element.denote_add cast cast_zero cast_one cast_add cast_sub cast_mul cast_nat cast_sign cast_neg cast_inv a b
private theorem read_sub (a b : Element FiniteTower.first) : read (a - b) = read a - read b :=
  Element.denote_sub cast cast_zero cast_one cast_add cast_sub cast_mul cast_nat cast_sign cast_neg cast_inv a b
private theorem read_mul (a b : Element FiniteTower.first) : read (a * b) = read a * read b :=
  Element.denote_mul cast cast_zero cast_one cast_add cast_sub cast_mul cast_nat cast_sign cast_neg cast_inv a b
private theorem read_nat (n : Nat) : read n = (n : ℝ) :=
  Element.denote_nat cast cast_zero cast_one cast_add cast_sub cast_mul cast_nat cast_sign cast_neg cast_inv n
private theorem read_sign (a : Element FiniteTower.first) : a.sign = (SignType.sign (read a) : Int) :=
  a.sign_spec cast cast_zero cast_one cast_add cast_sub cast_mul cast_nat cast_sign cast_neg cast_inv

/-- The ordinary real root selected by the retained nested descriptor. -/
noncomputable def beta : ℝ := FiniteTowerUse.next.rootValue
  read read_zero read_one read_add read_sub read_mul read_nat read_sign

private theorem first_head :
    interpret cast cast_zero FiniteTower.firstRaw.head = Polynomial.X ^ 2 - Polynomial.C (2 : ℝ) := by
  apply Polynomial.ext
  intro i
  obtain rfl | rfl | rfl | hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i := by omega
  all_goals simp [coeff_interpret, FiniteTower.firstRaw, DensePoly.coeff_ofCoeffs,
    Polynomial.coeff_X_pow, cast, Array.getD]
  simp [show ¬ i < 3 by omega, show i ≠ 2 by omega, Polynomial.coeff_C,
    show i ≠ 0 by omega]
  rfl

/-- The actual retained first descriptor selects the positive square root of two. -/
theorem alpha_square : alpha ^ 2 = 2 := by
  have h := FiniteTower.first.evalPoly_head
    cast cast_zero cast_one cast_add cast_sub cast_mul cast_nat cast_sign
  change (interpret cast cast_zero FiniteTower.first.root.raw.head).eval alpha = 0 at h
  rw [show FiniteTower.first.root.raw = FiniteTower.firstRaw by
    rw [FiniteTower.first, Context.root_adjoin, FiniteTower.firstRoot_raw], first_head] at h
  simpa using (sub_eq_zero.mp (by simpa using h : alpha ^ 2 - 2 = 0))

private theorem read_neg (a : Element FiniteTower.first) : read (-a) = -read a :=
  Element.denote_neg cast cast_zero cast_one cast_add cast_sub cast_mul cast_nat cast_sign cast_neg cast_inv a

/-- The retained literal generator denotes the selected first root. -/
theorem read_generator : read FiniteTower.generator = alpha := by
  change (interpret cast cast_zero FiniteTower.generator.polynomial).eval alpha = alpha
  rw [show FiniteTower.generator.polynomial = FiniteTower.variablePoly by
    apply Element.restore_polynomial]
  have hx : interpret cast cast_zero FiniteTower.variablePoly = Polynomial.X := by
    apply Polynomial.ext
    intro i
    obtain rfl | rfl | hi : i = 0 ∨ i = 1 ∨ 2 ≤ i := by omega
    all_goals simp [coeff_interpret, FiniteTower.variablePoly, DensePoly.coeff_ofCoeffs,
      Polynomial.coeff_X, cast, Array.getD]
    simp [show ¬ i ≤ 1 by omega, show 1 ≠ i by omega]
    rfl
  rw [hx, Polynomial.eval_X]

/-- The selected first root lies in its original open rational interval. -/
theorem alpha_interval : 1 < alpha ∧ alpha < 2 := by
  have h := (FiniteTower.first.root.root_spec
    cast cast_zero cast_one cast_add cast_sub cast_mul cast_nat cast_sign).1
  have h := ((Tarski.mem_rootsIn _ _ _ _).mp h).2
  rw [show FiniteTower.first.root.raw = FiniteTower.firstRaw by
    rw [FiniteTower.first, Context.root_adjoin, FiniteTower.firstRoot_raw]] at h
  simpa [FiniteTower.firstRaw, Endpoint.map, cast, alpha, Context.rootValue, Tarski.inInterval_finite] using h

private theorem next_head :
    interpret read read_zero FiniteTower.nextRaw.head = Polynomial.X ^ 2 - Polynomial.C alpha := by
  apply Polynomial.ext
  intro i
  obtain rfl | rfl | rfl | hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i := by omega
  all_goals simp [coeff_interpret, FiniteTower.nextRaw, DensePoly.coeff_ofCoeffs,
    Polynomial.coeff_X_pow, Polynomial.coeff_C, Array.getD,
    read_neg, read_generator, read_one, (read_zero 0).mpr rfl]
  simp [show ¬ i < 3 by omega, show i ≠ 2 by omega, show i ≠ 0 by omega]
  exact (read_zero 0).mpr rfl

/-- The selected nested root satisfies its original equation over the first root. -/
theorem beta_square : beta ^ 2 = alpha := by
  have h := FiniteTowerUse.next.evalPoly_head
    read read_zero read_one read_add read_sub read_mul read_nat read_sign
  change (interpret read read_zero FiniteTowerUse.next.root.raw.head).eval beta = 0 at h
  rw [FiniteTowerUse.next_raw, next_head] at h
  exact sub_eq_zero.mp (by simpa using h : beta ^ 2 - alpha = 0)

/-- The same nested root lies in its original open rational interval. -/
theorem beta_interval : 1 < beta ∧ beta < 2 := by
  have h := (FiniteTowerUse.next.root.root_spec
    read read_zero read_one read_add read_sub read_mul read_nat read_sign).1
  have h := ((Tarski.mem_rootsIn _ _ _ _).mp h).2
  rw [FiniteTowerUse.next_raw] at h
  have h2 : read (2 : Element FiniteTower.first) = 2 := read_nat 2
  simpa [FiniteTower.nextRaw, Endpoint.map, read_one, h2,
    beta, Context.rootValue, Tarski.inInterval_finite] using h

/-- The actual two retained selected descriptors give the positive fourth root of two. -/
theorem beta_fourth : beta ^ 4 = 2 := by
  calc
    beta ^ 4 = (beta ^ 2) ^ 2 := by ring
    _ = 2 := by rw [beta_square, alpha_square]

/-- The first value is the ordinary positive square root, with no new root choice. -/
theorem alpha_sqrt : alpha = Real.sqrt 2 := by
  symm
  apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by linarith [alpha_interval])).mpr
  exact alpha_square.symm

/-- The nested value is the ordinary positive square root of the first value. -/
theorem beta_sqrt : beta = Real.sqrt alpha := by
  symm
  apply (Real.sqrt_eq_iff_eq_sq (by linarith [alpha_interval])
    (by linarith [beta_interval])).mpr
  exact beta_square.symm

/-- The retained nested descriptor selects this same ordinary real point for
its head, endpoints and complete derivative-sign list. -/
theorem beta_selected :
    beta ∈ Tarski.rootsIn (interpret read read_zero FiniteTowerUse.next.root.raw.head)
      (FiniteTowerUse.next.root.raw.lower.map read) (FiniteTowerUse.next.root.raw.upper.map read) ∧
    signsAt read read_zero FiniteTowerUse.next.root.raw.queries beta = FiniteTowerUse.next.root.raw.signs :=
  FiniteTowerUse.next.root.root_spec read read_zero read_one read_add read_sub read_mul read_nat read_sign

end Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.beta_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.beta_selected

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.read_generator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.read_generator

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.alpha_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.alpha_square

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.alpha_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.alpha_interval

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.beta_square' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.beta_square

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.beta_interval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.beta_interval

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.beta_fourth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.beta_fourth

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.alpha_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.alpha_sqrt

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.beta_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.FiniteTowerReal.beta_sqrt
