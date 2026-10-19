/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.RowOperations
public section
namespace Hex.RCF.RealCoefficients.RowReplay
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}

/-- Decode and check one whole row bound to the exact supplied descriptor and
ordered query list. All original guards are checked before decoding. -/
@[expose] def read (value : ValueCodec parent.Value) (guards : List parent.Value)
    (root : Descriptor parent.Value Signature parent.sign parent.signature)
    (queries : List (DensePoly parent.Value)) (packet : Codec.Json) :
    Except Replay.Error (SelectedSigns root queries) := do
  unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw .divisor
  RowOperations.read value Signature.codec parent.sign parent.signature root queries packet
end Hex.RCF.RealCoefficients.RowReplay
