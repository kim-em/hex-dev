/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexLatticeEnum
import Lean.Data.Json

open Hex Hex.LatticeEnum Lean

namespace Hex.LatticeEnum.Emit

private def encodePoint (p : Point n m) : Json := Json.mkObj
  [("coefficients", toJson p.coefficients.toList), ("ambient", toJson p.ambient.toList),
    ("distanceSq", toJson (toString p.distanceSq))]

private def emit (id : String) (rows : Matrix Int n m) (t : Vector Rat m) (r : Rat) : IO Unit := do
  let out ← IO.getStdout
  let write := fun (op status : String) (radius : Rat) (ps : List (Point n m)) =>
    out.putStrLn (Json.mkObj [("schema_version", toJson (1 : Nat)), ("id", toJson id),
      ("operation", toJson op), ("n", toJson n), ("m", toJson m),
      ("basis", toJson (rows.rows.toList.map Vector.toList)),
      ("target", toJson (t.toList.map toString)), ("radiusSq", toJson (toString radius)),
      ("status", toJson status), ("points", toJson (ps.map encodePoint))]).compress
  let some b := ofMatrix? rows | write "enumerate" "rejected" r []; return
  write "enumerate" "complete" r (enumerate b t r)
  write "babai" "candidate" r [babai b t]
  let cv := closest b t
  write "closest" "complete" cv.distanceSq cv.points
  if t == 0 then
    match shortest b with
    | none => write "shortest" "none" 0 []
    | some sv => write "shortest" "complete" sv.distanceSq sv.points
  for budget in [{ nodes := some 0 }, { answers := some 1 }, { certificateNodes := some 2 }] do
    match enumerateWith budget b t r with
    | .complete ps _ _ => write "enumerate" "complete" r ps
    | .incomplete ps _ _ => write "enumerate" "incomplete" r ps

def run : IO Unit := do
  emit "rank-zero" (Matrix.ofRows (#v[] : Vector (Vector Int 2) 0)) #v[3, 4] 25
  emit "rank-zero-outside" (Matrix.ofRows (#v[] : Vector (Vector Int 2) 0)) #v[3, 4] 24
  emit "empty-ambient" (Matrix.ofRows (#v[] : Vector (Vector Int 0) 0)) #v[] 0
  emit "dependent" (Matrix.ofRows #v[#v[1, 2], #v[2, 4]]) 0 5
  emit "a2" (Matrix.ofRows #v[#v[1, -1, 0], #v[0, 1, -1]]) 0 2
  emit "a2-shell" (Matrix.ofRows #v[#v[1, -1, 0], #v[0, 1, -1]]) 0 6
  emit "rectangular" (Matrix.ofRows #v[#v[2, 0, 0], #v[0, 3, 0]]) #v[1, 3/2, 2] (29/4)
  emit "babai-gap" (Matrix.ofRows #v[#v[2, 0], #v[1, 2]]) #v[1, 1] 2
  emit "square-ties" (Matrix.ofRows #v[#v[1, 0], #v[0, 1]]) #v[1/2, 1/2] (1/2)
  emit "negative-radius" (Matrix.ofRows #v[#v[1]]) #v[0] (-1)
  emit "zero-radius" (Matrix.ofRows #v[#v[1]]) #v[0] 0
  emit "negative-coefficients" (Matrix.ofRows #v[#v[1]]) #v[-2001/2] (1/4)
  emit "wide-integers" (Matrix.ofRows #v[#v[2^80]]) #v[(2^80 : Rat) / 3] ((2^160 : Rat) / 9)
  for shear in [0, 1, 3, -3] do
    for u in [-1, 0, 1] do
      emit s!"shear-{shear}-target-{u}" (Matrix.ofRows #v[#v[1, shear], #v[0, 1]])
        #v[(u : Rat) / 2, 1/3] (13/9)

end Hex.LatticeEnum.Emit

def main : IO Unit := Hex.LatticeEnum.Emit.run
