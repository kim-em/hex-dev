/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RootQuoteCases
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

end Hex.RCF.RootQuoteTests
