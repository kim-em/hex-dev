/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardJointPublic
public import KernelReplay.FramePublic

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardJointUse

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
/-- Public clients can eliminate the joint existential through an ordinary
module import, without loading private implementation bodies. -/
theorem exists_points : ∃ first second : Real, first = first ∧ second = second := by
  exact Exists.elim GuardJointPublic.exists_points fun _ firstExists =>
    Exists.elim firstExists fun first secondExists =>
      Exists.elim secondExists fun second _ => ⟨first, second, rfl, rfl⟩

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.GuardJointUse.exists_points' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_points


local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat
local instance : Field (Hex.RationalFn (Hex.RationalFn Rat)) := HexPolyTheory.fieldOfGrind

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
/-- Both original defining equations and the native product hold at the same
ordinary real coordinates and coefficient interpretation. -/
theorem coordinates : ∃ interpretation, ∃ alpha beta : Real,
    (HexPolyTheory.Interpret.interpret (fun y : Real => y) (fun _ => Iff.rfl)
      (Hex.RealClosure.Transport.polynomial
        (FiniteBaseProbe.base.partialRead interpretation) FrameOwners.firstRaw.head)).eval alpha = 0 ∧
    (HexPolyTheory.Interpret.interpret (fun y : Real => y) (fun _ => Iff.rfl)
      (Hex.RealClosure.Transport.polynomial
        (FramePublic.firstReader interpretation alpha) FrameOwners.secondRaw.head)).eval beta = 0 ∧
    FramePublic.nativeSquare interpretation alpha beta =
      FramePublic.secondReader interpretation alpha beta FrameOwners.beta *
        FramePublic.secondReader interpretation alpha beta FrameOwners.beta := by
  rcases GuardJointPublic.exists_points with ⟨interpretation, alpha, beta, conditions⟩
  have first := conditions.1.1.1.1.1.1.1.1.1.1.2.1
  have second := conditions.1.1.1.1.1.1.1.1.1.1.2.2
  have product := conditions.2.2.2.2.2.2
  have firstRoot := (Polynomial.isRoot_of_mem_roots
    ((HexRealRootsTheory.Tarski.mem_rootsIn _ _ _ _).mp first.selected.1).1).eq_zero
  have secondRoot := (Polynomial.isRoot_of_mem_roots
    ((HexRealRootsTheory.Tarski.mem_rootsIn _ _ _ _).mp second.selected.1).1).eq_zero
  change (HexPolyTheory.Interpret.interpret (fun y : Real => y) (fun _ => Iff.rfl)
    (Hex.RealClosure.Transport.polynomial
      (FiniteBaseProbe.base.partialRead interpretation) FrameOwners.first.root.raw.head)).eval alpha = 0
    at firstRoot
  change (HexPolyTheory.Interpret.interpret (fun y : Real => y) (fun _ => Iff.rfl)
    (Hex.RealClosure.Transport.polynomial
      (FramePublic.firstReader interpretation alpha) FrameOwners.second.root.raw.head)).eval beta = 0
    at secondRoot
  rw [FrameOwners.first_raw] at firstRoot
  rw [FrameOwners.second_raw] at secondRoot
  have bound : 0 < FrameOwners.requestPoly.size := by
    rw [← GuardOperand.polynomialNative]
    exact Nat.zero_lt_succ 0
  have coefficient : FrameOwners.requestPoly.coeff 0 = FrameOwners.beta := by
    rw [← GuardOperand.polynomialNative]
    exact GuardOperand.betaNative
  have nativeProduct := product.products 0 bound 0 bound
  rw [coefficient] at nativeProduct
  exact ⟨interpretation, alpha, beta, firstRoot, secondRoot, nativeProduct⟩

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.GuardJointUse.coordinates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coordinates

end Hex.RealClosure.Algebraic.KernelReplay.GuardJointUse
