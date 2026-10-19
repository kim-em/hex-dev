/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedTransport.Context
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Constants
open Hex.RCF.RealCoefficients.NestedTransportTests.Context
def constant (a : Hex.RCF.RealCoefficients.RootTransportData.conversion.context.Value) :
    Algebraic.SignFact native :=
  ⟨DensePoly.C a, Hex.RCF.RealCoefficients.RootTransportData.conversion.context.sign a, by
    rw [Algebraic.Context.signPoly_const native (DensePoly.C a)
      (DensePoly.size_ofCoeffs_le #[a]), DensePoly.coeff_C]
    rfl⟩
end Hex.RCF.RealCoefficients.NestedTransportTests.Constants
