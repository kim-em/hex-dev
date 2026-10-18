/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexSignDet.Conformance
public import Mathlib.Algebra.Field.Rat
public section
namespace Hex.RCF.TreeQuote
open Hex Hex.SignDet

@[expose] def leafTrue : Except String Nat :=
  if (Replay.leaf Conformance.literalNode).check Sturm.orderSign 7
      Sturm.Fixtures.p (.finite (-2)) (.finite 2) [] = true then .ok 7 else .error "leaf refused"
@[expose] def leafFalse : Except String Nat :=
  if (Replay.leaf Conformance.literalNode).check Sturm.orderSign 8
      Sturm.Fixtures.p (.finite (-2)) (.finite 2) [] = true then .error "wrong context accepted" else .ok 29
@[expose] def splitTrue : Except String Nat :=
  if Conformance.fullReplay.check Sturm.orderSign 7 Conformance.singletonRaw.head
      Conformance.singletonRaw.lower Conformance.singletonRaw.upper
      (Conformance.singletonRaw.full []).queries = true then .ok 31 else .error "split refused"
@[expose] def splitFalse : Except String Nat :=
  if (Replay.split Conformance.fullNode (.leaf Conformance.derivativeNode)
      (.leaf Conformance.firstNode)).check Sturm.orderSign 7 Conformance.singletonRaw.head
      Conformance.singletonRaw.lower Conformance.singletonRaw.upper
      (Conformance.singletonRaw.full []).queries = true then .error "swapped children accepted" else .ok 37
@[expose] def wrongContext : Except String Nat :=
  if (Replay.leaf Conformance.literalNode).check Sturm.orderSign 8
      Sturm.Fixtures.p (.finite (-2)) (.finite 2) [] = true then .ok 7 else .error "wrong context"
@[expose] def swappedChildren : Except String Nat :=
  if (Replay.split Conformance.fullNode (.leaf Conformance.derivativeNode)
      (.leaf Conformance.firstNode)).check Sturm.orderSign 7 Conformance.singletonRaw.head
      Conformance.singletonRaw.lower Conformance.singletonRaw.upper
      (Conformance.singletonRaw.full []).queries = true then .ok 31 else .error "swapped children"

end Hex.RCF.TreeQuote
