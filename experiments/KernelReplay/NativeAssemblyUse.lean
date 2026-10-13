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

theorem joint : statement := exists_joint

theorem sourceContext : source := source_binding

/-- A public consumer unfolds the exposed statement and uses its coordinate
and its requested sum conjunct, rather than accepting an opaque proposition. -/
theorem coordinate : ∃ point : Real, True := by
  rcases exists_joint with
    ⟨interpretation, point, base, domain, conditions, g₁, g₂, g₃, g₄, g₅, g₆, g₇, sum, done⟩
  change Hex.RealClosure.Transport.Sum _ _ _ at sum
  exact ⟨point, trivial⟩

theorem originalContext : ∃ original : Hex.RealClosure.Tower.Context FiniteBaseProbe.registry,
    context = original := by
  exact ⟨_, source_binding.1⟩

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.exists_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.exists_joint

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyUse.coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coordinate

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyUse.originalContext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms originalContext

end Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyUse
