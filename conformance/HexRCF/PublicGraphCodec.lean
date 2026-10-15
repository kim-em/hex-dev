/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients

public section
open Hex Hex.SignDet

namespace Hex.RCF.PublicGraphCodec

/-- The optional umbrella exposes the graph reader for kernel reduction. -/
theorem graph_empty : (Codec.readGraph ValueCodec.rat ValueCodec.nat (0 : Nat)
    (DensePoly.ofList ([1] : List Rat)) .negInf .posInf (.arr #[])).toOption.isNone = true := by
  decide +kernel

/-- info: 'Hex.RCF.PublicGraphCodec.graph_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms graph_empty

end Hex.RCF.PublicGraphCodec
