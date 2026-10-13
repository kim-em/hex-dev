/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedTransport.Fields
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Restore
open Hex.RCF.RealCoefficients.NestedTransportTests.Context
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
@[macro_inline] def restore (required : List (DensePoly Data.parent.Value))
    (evidence : Algebraic.SignEvidence Data.parent.Value Signature)
    (accepted : (native.readEvidence? Data.original.value Data.original.zero_iff Data.original.one
      Data.original.add Data.original.sub Data.original.mul Data.original.nat Data.original.sign
      Data.original.neg Data.original.inv required evidence).isSome = true)
    (i : Fin required.length) : Algebraic.SignFact native :=
  let result := native.readEvidence? Data.original.value Data.original.zero_iff Data.original.one
    Data.original.add Data.original.sub Data.original.mul Data.original.nat Data.original.sign
    Data.original.neg Data.original.inv required evidence
  let facts := result.get accepted
  let binding := Hex.RCF.RealCoefficients.NestedTransportTests.Fields.fields required evidence facts
    (Option.some_get accepted).symm i
  let literal := evidence.values.toList[i.val]?
  let nonempty : literal.isSome = true := by change (evidence.values.toList[i.val]?).isSome = true; rw [← binding.2]; rfl
  { polynomial := required[i.val]
    sign := literal.get nonempty
    checked := by
      have signs : (facts[i.val]).sign = literal.get nonempty := by
        apply Option.some.inj
        exact binding.2.trans (Option.some_get nonempty).symm
      rw [← binding.1, ← signs]
      exact (facts[i.val]).checked }
end Hex.RCF.RealCoefficients.NestedTransportTests.Restore
