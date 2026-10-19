/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardProduct

public section
namespace Hex.RealClosure.Algebraic.KernelReplay.GuardProductPublic

/-- The retained operand is the actual original native second generator. -/
theorem operand : GuardOperand.beta = FrameOwners.beta := GuardOperand.betaNative

/-- The polynomial is the actual original native product operand. -/
theorem polynomial : GuardOperand.polynomial = FrameOwners.requestPoly :=
  GuardOperand.polynomialNative

/-- The original native product uses the same second reader as the complete inventory. -/
theorem product : Transport.Product GuardSecondData.reader
    FrameOwners.requestPoly FrameOwners.requestPoly := GuardProduct.nativeProduct

end Hex.RealClosure.Algebraic.KernelReplay.GuardProductPublic
