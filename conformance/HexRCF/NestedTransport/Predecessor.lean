/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RootTransportConformance
import HexRCF.SelectedRoot.RowCollect
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor
open Data
private def scalar := Hex.RCF.RealCoefficients.RootTransportConformance.constant
/-- Fourteen proved rational literals supplement the retained first-field
scalar inventory. This fixed-parent fixture does not authenticate arbitrary
provider or context history. -/
def facts : List (Algebraic.SignFact native) :=
  [scalar (3/2), scalar (-4/3), scalar 3, scalar (4/3),
    scalar (2/9), scalar (-1/2), scalar 8, scalar (1/2),
    scalar (7/4), scalar (9/4), scalar (-8/9), scalar (9/2),
    scalar (8/9), scalar (98/81)] ++ RowCollect.facts
#print axioms facts
end Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor
