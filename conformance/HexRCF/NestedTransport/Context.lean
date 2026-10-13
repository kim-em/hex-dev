/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RootTransportConformance
import HexRCF.NestedTransport.Frame
import HexRCF.SelectedRoot.Upper
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
open Hex.RCF.RealCoefficients
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Context
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
def first := RootTransport.step RootTransportData.conversion Data.lower
  RootTransportConformance.checked.converted RootTransportConformance.checked.binding
def conversion := first.cast Data.parent_eq
def chain := Chain.root (.base (BaseContext.rational Data.registry)) Data.lower
  Data.frozenFrame Data.frameEncoded
def descriptor := RootTransportConformance.checked.converted
def extension := Data.parent.adjoin descriptor
def target : Context Data.registry :=
  .pack (.root chain descriptor Hex.RCF.RealCoefficients.NestedTransportTests.Frame.frame Hex.RCF.RealCoefficients.NestedTransportTests.Frame.encoded)
def native := Algebraic.Context.adjoin descriptor Data.parent.isClean
theorem context_eq : conversion.context = target := by
  exact (Conversion.cast_spec first Data.parent_eq).1.trans
    ((RootTransport.step_spec RootTransportData.conversion Data.lower descriptor
      RootTransportConformance.checked.binding).1.trans (Tower.Context.adjoin_root_eq chain descriptor Hex.RCF.RealCoefficients.NestedTransportTests.Frame.frame Hex.RCF.RealCoefficients.NestedTransportTests.Frame.encoded))
#print axioms context_eq
theorem polynomial (a : Data.parent.Value) :
    Data.base.polynomial Data.lower (_root_.cast (congrArg Context.Value Data.parent_eq.symm) a) =
      Algebraic.Element.polynomial a := by
  simp only [Tower.Context.polynomial, cast_cast]
  rfl

theorem signature_eq : target.signature = Hex.RCF.RealCoefficients.NestedTransportTests.Frame.signature := by decide +kernel
#print axioms signature_eq
end Hex.RCF.RealCoefficients.NestedTransportTests.Context
