/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.NativeAssemblyUse

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyNested
open Hex.SignDet

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat

/-- Two checked selected extensions above the actual successive-infinitesimal
base. The second polynomial uses the first extension's typed generator. -/
@[expose] def context : Tower.Context FiniteBaseProbe.registry :=
  match Descriptor.validate NativeAssemblyStaged.base.sign
      NativeAssemblyStaged.base.signature NativeAssemblyStaged.raw with
  | none => NativeAssemblyStaged.base
  | some first =>
    let extension := NativeAssemblyStaged.base.adjoin first
    let parent := extension.context
    let raw : RawDescriptor parent.Value Tower.Signature :=
      ⟨parent.signature, DensePoly.ofCoeffs #[-extension.generator, 0, 1],
        .negInf, .posInf, [1], [1]⟩
    match Descriptor.validate parent.sign parent.signature raw with
    | none => parent
    | some second => (parent.adjoin second).context

end Hex.RealClosure.Algebraic.KernelReplay.NativeAssemblyNested
