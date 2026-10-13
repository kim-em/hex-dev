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

/-- info: 'Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.exists_joint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyStaged.exists_joint

end Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyUse
