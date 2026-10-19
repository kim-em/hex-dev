/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.NativeAssemblyStaged

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyUse

open Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat
local instance : Field (Hex.RationalFn (Hex.RationalFn Rat)) := HexPolyTheory.fieldOfGrind

noncomputable def reader
    (interpretation : Hex.RealClosure.CoefficientMap (Hex.RationalFn (Hex.RationalFn Rat)) Real)
    (point : Real) (value : Element owner) : Real :=
  Packing.eval (FiniteBaseProbe.base.partialRead interpretation) point value.polynomial

theorem joint : statement := exists_joint

theorem sourceContext : source := source_binding

/-- The requested coefficient sum holds at the same ordinary real coordinate
and coefficient interpretation returned by the joint realization. -/
theorem coordinate : ∃ interpretation, ∃ point : Real,
    (HexPolyTheory.Interpret.interpret (fun y : Real => y) (fun _ => Iff.rfl)
      (Hex.RealClosure.Transport.polynomial
        (FiniteBaseProbe.base.partialRead interpretation) raw.head)).eval point = 0 ∧
    reader interpretation point (requestPoly.coeff 0 + requestPoly.coeff 0) =
      reader interpretation point (requestPoly.coeff 0) +
        reader interpretation point (requestPoly.coeff 0) := by
  rcases exists_joint with
    ⟨interpretation, point, base, domain, conditions, g₁, g₂, g₃, g₄, g₅, g₆, g₇, sum, done⟩
  change Hex.RealClosure.Transport.Sum (reader interpretation point) requestPoly requestPoly at sum
  have selected := conditions.selected.1
  have root := (Polynomial.isRoot_of_mem_roots
    ((HexRealRootsTheory.Tarski.mem_rootsIn _ _ _ _).mp selected).1).eq_zero
  change (HexPolyTheory.Interpret.interpret (fun y : Real => y) (fun _ => Iff.rfl)
    (Hex.RealClosure.Transport.polynomial
      (FiniteBaseProbe.base.partialRead interpretation) owner.root.raw.head)).eval point = 0 at root
  rw [root_raw] at root
  exact ⟨interpretation, point, root, sum.sums 0 request_bound⟩

theorem originalContext : owner.root.raw = raw := root_raw

theorem selectedContext : context = (base.adjoin owner.root).context := by
  unfold context
  rw [validated]

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.exists_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.exists_joint

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyUse.coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coordinate

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyUse.originalContext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms originalContext

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyUse.selectedContext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selectedContext

end Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyUse
