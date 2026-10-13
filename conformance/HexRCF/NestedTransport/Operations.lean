/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedTransport.Context
import HexRCF.SelectedRoot.KernelCheck
import HexRCF.NestedTransport.Predecessor
import HexRealClosure.FactOperations
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Operations
open Hex.RCF.RealCoefficients.NestedTransportTests.Context
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
@[instance_reducible] def one (prior : List (Algebraic.SignFact Data.native)) :=
  Algebraic.Element.cachedOne Data.reduction Data.reduction_eq prior
@[instance_reducible] def add (prior : List (Algebraic.SignFact Data.native)) :=
  Algebraic.Element.cachedAdd Data.reduction Data.reduction_eq prior
@[instance_reducible] def sub (prior : List (Algebraic.SignFact Data.native)) :=
  Algebraic.Element.cachedSub Data.reduction Data.reduction_eq prior
@[instance_reducible] def mul (prior : List (Algebraic.SignFact Data.native)) :=
  Algebraic.Element.cachedMul Data.reduction Data.reduction_eq prior
theorem one_eq (prior : List (Algebraic.SignFact Data.native)) :
    one prior = (inferInstance : One Data.parent.Value) := Algebraic.Element.cachedOne_eq Data.reduction Data.reduction_eq prior
theorem add_eq (prior : List (Algebraic.SignFact Data.native)) :
    add prior = (inferInstance : Add Data.parent.Value) := Algebraic.Element.cachedAdd_eq Data.reduction Data.reduction_eq prior
theorem sub_eq (prior : List (Algebraic.SignFact Data.native)) :
    sub prior = (inferInstance : Sub Data.parent.Value) := Algebraic.Element.cachedSub_eq Data.reduction Data.reduction_eq prior
theorem mul_eq (prior : List (Algebraic.SignFact Data.native)) :
    mul prior = (inferInstance : Mul Data.parent.Value) := Algebraic.Element.cachedMul_eq Data.reduction Data.reduction_eq prior
theorem policy : native.canReduce = true := by
  rw [native.reduce_checked]
  have unit : (1 : Hex.RCF.RealCoefficients.RootTransportData.conversion.context.Value) =
      @One.one Hex.RCF.RealCoefficients.RootTransportData.conversion.context.Value
        (one Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts) :=
    (congrArg (@One.one Hex.RCF.RealCoefficients.RootTransportData.conversion.context.Value)
      (one_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)).symm
  rw [unit]
  decide +kernel
def reduce (prior : List (Algebraic.SignFact Data.native))
    (p : DensePoly Hex.RCF.RealCoefficients.RootTransportData.conversion.context.Value) :=
  letI := one prior
  letI := sub prior
  letI := mul prior
  let monic : native.root.raw.head.leadingCoeff = @One.one
      Hex.RCF.RealCoefficients.RootTransportData.conversion.context.Value (one prior) :=
    (native.monic_of_reduce policy).trans
      (congrArg (@One.one Hex.RCF.RealCoefficients.RootTransportData.conversion.context.Value)
        (one_eq prior)).symm
  (@DensePoly.divModMonic
    Hex.RCF.RealCoefficients.RootTransportData.conversion.context.Value
    (Tower.instZeroValue Hex.RCF.RealCoefficients.RootTransportData.conversion.context)
    (Tower.instDecidableEqValue Hex.RCF.RealCoefficients.RootTransportData.conversion.context)
    (one prior)
    (Tower.instAddValue Hex.RCF.RealCoefficients.RootTransportData.conversion.context)
    (sub prior) (mul prior) p native.root.raw.head monic).2
theorem reduce_eq (prior : List (Algebraic.SignFact Data.native)) : reduce prior = native.reduce := by
  have supplied := native.factReduce_eq (one prior) (sub prior) (mul prior)
    (one_eq prior) (sub_eq prior) (mul_eq prior)
  refine Eq.trans ?_ supplied
  funext p
  simp only [reduce, Algebraic.Context.factReduce, policy, ↓reduceDIte]
@[instance_reducible] def higherOne facts prior := Algebraic.Element.factOne (one prior) (one_eq prior)
  (reduce prior) (reduce_eq prior) facts
@[instance_reducible] def higherAdd facts prior := Algebraic.Element.factAdd (add prior) (add_eq prior)
  (reduce prior) (reduce_eq prior) facts
@[instance_reducible] def higherSub facts prior := Algebraic.Element.factSub (sub prior) (sub_eq prior)
  (reduce prior) (reduce_eq prior) facts
@[instance_reducible] def higherMul facts prior := Algebraic.Element.factMul (add prior) (mul prior) (add_eq prior) (mul_eq prior)
  (reduce prior) (reduce_eq prior) facts
@[instance_reducible] def higherNat facts prior := Algebraic.Element.factNatCast
  (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq prior)
  (Algebraic.Element.cachedNatCast_eq Data.reduction Data.reduction_eq prior)
  (reduce prior) (reduce_eq prior) facts
theorem higherOne_eq (facts : List (Algebraic.SignFact native))
    (prior : List (Algebraic.SignFact Data.native)) :
    higherOne facts prior = (inferInstance : One target.Value) :=
  Algebraic.Element.factOne_eq (one prior) (one_eq prior) (reduce prior) (reduce_eq prior) facts
theorem higherAdd_eq (facts : List (Algebraic.SignFact native))
    (prior : List (Algebraic.SignFact Data.native)) :
    higherAdd facts prior = (inferInstance : Add target.Value) :=
  Algebraic.Element.factAdd_eq (add prior) (add_eq prior) (reduce prior) (reduce_eq prior) facts
theorem higherSub_eq (facts : List (Algebraic.SignFact native))
    (prior : List (Algebraic.SignFact Data.native)) :
    higherSub facts prior = (inferInstance : Sub target.Value) :=
  Algebraic.Element.factSub_eq (sub prior) (sub_eq prior) (reduce prior) (reduce_eq prior) facts
theorem higherMul_eq (facts : List (Algebraic.SignFact native))
    (prior : List (Algebraic.SignFact Data.native)) :
    higherMul facts prior = (inferInstance : Mul target.Value) :=
  Algebraic.Element.factMul_eq (add prior) (mul prior) (add_eq prior) (mul_eq prior) (reduce prior) (reduce_eq prior) facts
theorem higherNat_eq (facts : List (Algebraic.SignFact native))
    (prior : List (Algebraic.SignFact Data.native)) :
    higherNat facts prior = (inferInstance : NatCast target.Value) :=
  Algebraic.Element.factNatCast_eq
    (Algebraic.Element.cachedNatCast Data.reduction Data.reduction_eq prior)
    (Algebraic.Element.cachedNatCast_eq Data.reduction Data.reduction_eq prior)
    (reduce prior) (reduce_eq prior) facts
open Lean in
run_meta do
  let .thmInfo info ← getConstInfo ``policy
    | throwError "expected policy proof"
  KernelCheck.addChecked `Hex.RCF.RealCoefficients.NestedTransportTests.Operations.policyChecked info.type info.value
    #[``Descriptor.validate, ``Descriptor.ofReplay?]
end Hex.RCF.RealCoefficients.NestedTransportTests.Operations
