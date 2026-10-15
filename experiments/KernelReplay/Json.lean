/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean
public import HexSignDet.Codec.Json
public meta import HexSignDet.Codec.Json
public meta import HexRealClosureTheory.NativeRecords

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay
open Lean Hex.SignDet

/-- Change one literal JSON field only when its previous value is exactly the
expected input. Used to make certificate mutations independent of decoding. -/
def replace (j : Codec.Json) (path : List Nat) (expected value : Codec.Json) :
    Option Codec.Json := do
  match path with
  | [] => if j = expected then some value else none
  | i :: rest =>
    let values ← j.getArr?.toOption
    let old ← values[i]?
    let changed ← replace old rest expected value
    return Codec.Json.arr (values.set! i changed)

end Hex.RealClosure.Algebraic.KernelReplay
