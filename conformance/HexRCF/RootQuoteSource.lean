/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RootQuoteCases
public import HexRealClosureTheory.NumberFieldTower
public section
open Hex Hex.RealClosure Hex.SignDet
namespace Hex.RCF.RootQuoteTests

theorem reader_ok : read = .ok nativeRoot := by
  have certified := nativeRoot_read
  cases equation : read with
  | error message => simp [equation,Except.toOption] at certified
  | ok root =>
    have same : root = nativeRoot := by
      simpa only [equation,Except.toOption,Option.some.injEq] using certified
    exact congrArg Except.ok same

theorem root_raw : nativeRoot.raw = rawSubject := by
  have consumed := Algebraic.RootReplay.readDescriptor_subject base.codec
    (Tower.contextCodec base.signature) base.sign base.signature subject evidence
    nativeRoot reader_ok
  have same := subject_read.symm.trans consumed
  exact (Except.ok.inj same).symm

theorem root_subject :
    nativeRoot.raw.context = base.signature ∧
    nativeRoot.raw.head = DensePoly.ofCoeffs #[⟨(-3 : Rat)⟩,⟨0⟩,⟨0⟩,⟨1⟩] ∧
    nativeRoot.raw.lower = .finite (⟨(-8 : Rat)⟩ : base.Value) ∧
    nativeRoot.raw.upper = .finite (⟨(8 : Rat)⟩ : base.Value) ∧
    nativeRoot.raw.indices = [] ∧ nativeRoot.raw.signs = [] := by
  rw [root_raw]
  refine ⟨rfl,?_,rfl,rfl,rfl,rfl⟩
  exact (DensePoly.ofCoeffs_toArray cubicHead).symm

open HexPolyTheory.Interpret HexRealRootsTheory

@[expose] noncomputable def realModel : Tower.Model base ℝ :=
  Tower.Model.base (BaseContext.rational registry) (Rat.castHom ℝ) ratSign

theorem rational_value (a : base.Value) : realModel.value a = (a.stored : ℝ) :=
  Tower.Model.base_value (BaseContext.rational registry) (Rat.castHom ℝ) ratSign a

theorem cubic_interpret : interpret realModel.value realModel.zero_iff cubicHead =
    (Polynomial.X ^ 3 - 3 : Polynomial ℝ) := by
  ext i
  rw [coeff_interpret, rational_value]
  rcases i with _ | _ | _ | _ | i
  · change ((-3 : Rat) : ℝ) = _
    norm_num
  · change ((0 : Rat) : ℝ) = _
    norm_num
  · change ((0 : Rat) : ℝ) = _
    norm_num
  · change ((1 : Rat) : ℝ) = _
    norm_num
  · have coefficient : cubicHead.coeff (i+1+1+1+1) = 0 :=
      DensePoly.coeff_eq_zero_of_size_le cubicHead (by change 4 ≤ i+1+1+1+1; omega)
    rw [coefficient]
    have zero := (BaseContext.Element.stored_eq_zero (0 : base.Value)).mpr rfl
    rw [zero]
    simp

@[expose] noncomputable def realRoot : ℝ :=
  nativeRoot.root realModel.value realModel.zero_iff realModel.one realModel.add
    realModel.sub realModel.mul realModel.nat realModel.sign

theorem realRoot_spec : realRoot ^ 3 = 3 ∧ -8 < realRoot ∧ realRoot < 8 := by
  have facts := (nativeRoot.root_spec realModel.value realModel.zero_iff realModel.one realModel.add
    realModel.sub realModel.mul realModel.nat realModel.sign).1
  change realRoot ∈ Tarski.rootsIn (interpret realModel.value realModel.zero_iff nativeRoot.raw.head)
    (nativeRoot.raw.lower.map realModel.value) (nativeRoot.raw.upper.map realModel.value) at facts
  rw [root_raw] at facts
  have nonzero : (Polynomial.X ^ 3 - 3 : Polynomial ℝ) ≠ 0 := by
    intro same
    have bad := congrArg (fun p : Polynomial ℝ => p.coeff 3) same
    norm_num at bad
  have nonzero' : interpret realModel.value realModel.zero_iff cubicHead ≠ 0 := by
    rw [cubic_interpret]
    exact nonzero
  change realRoot ∈ Tarski.rootsIn (interpret realModel.value realModel.zero_iff cubicHead)
    (.finite (realModel.value ⟨-8⟩)) (.finite (realModel.value ⟨8⟩)) at facts
  have present := (Tarski.mem_rootsIn_iff _ nonzero' _ _ realRoot).mp facts
  rw [cubic_interpret] at present
  have lower := rational_value (⟨(-8 : Rat)⟩ : base.Value)
  have upper := rational_value (⟨(8 : Rat)⟩ : base.Value)
  norm_num at lower upper
  rw [Tarski.inInterval_finite,lower,upper] at present
  simpa [Polynomial.eval_sub,Polynomial.eval_pow,
    Polynomial.eval_X,sub_eq_zero] using present

/-- The supplied frozen reader yields an ordinary real witness for its source polynomial. -/
theorem exists_cubic : ∃ x : ℝ, x ^ 3 = 3 ∧ -8 < x ∧ x < 8 :=
  ⟨realRoot,realRoot_spec⟩

end Hex.RCF.RootQuoteTests
