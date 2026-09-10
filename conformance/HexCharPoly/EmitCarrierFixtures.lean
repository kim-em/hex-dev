/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexCharPoly.Carriers

namespace Hex.CharPolyCarriers
open Hex Lean
local instance [ZMod64.Bounds p] : Zero (ZMod64 p) := ⟨0⟩

private def emit [Lean.Grind.CommRing R] [DecidableEq R]
    (encode : R → Json) (carrier : String) (arity : Nat) (entry : Nat → Nat → R) : IO Unit := do
  for (shape, n) in shapes do
    let A := matrix entry shape n
    let record := (request encode carrier shape arity A).setObjVal! "value"
      (.arr (A.charPoly.toArray.map encode))
    let line := record.compress ++ "\n"
    match ← IO.getEnv "HEX_FIXTURE_OUTPUT" with
    | none => IO.print line
    | some path =>
      let handle ← IO.FS.Handle.mk path .append
      handle.putStr line

def emitAll : IO Unit := do
  emit (denseJson intJson) "dense_int" 1 (denseEntry id 2)
  emit (denseJson ratJson) "dense_rat" 1 (denseEntry ratScalar 2)
  emit (denseJson modJson) "dense_mod" 1 (denseEntry (fun z => (z : Mod)) 2)
  for arity in [2, 3] do
    emit (mvJson intJson) "mv_int" arity (mvEntry id arity (if arity = 2 then 4 else 6))
    emit (mvJson ratJson) "mv_rat" arity (mvEntry ratScalar arity (if arity = 2 then 4 else 6))
  emit fractionJson "rat_fn" 1 (ratFnEntry 1)
end Hex.CharPolyCarriers

def main : IO Unit := Hex.CharPolyCarriers.emitAll
