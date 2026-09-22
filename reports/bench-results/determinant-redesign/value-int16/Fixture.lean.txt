/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDet.Select
import Lean

open Hex

namespace Determinant

abbrev Poly := MvPoly 2 Int Mono.grevlex

def entry (c : Int × Int × Int) : Poly :=
  MvPoly.C c.1 + MvPoly.C c.2.1 * MvPoly.X 1 +
    MvPoly.C c.2.2 * (MvPoly.X 0)^2

def coefficients : List (List (Int × Int × Int)) :=
  [[(-1,3,2), (2,-1,3), (4,2,-2), (-3,2,2)],
   [(1,-1,-3), (4,3,-2), (1,-2,3), (-1,-1,2)],
   [(2,-2,-1), (1,-2,-3), (4,-2,2), (-1,-1,-3)],
   [(4,2,-3), (-1,-1,1), (-1,3,1), (-1,-2,1)]]

def rows : List (List Poly) := coefficients.map (List.map entry)

def exportFixture : IO Unit := do
  let budget : Matrix.DetWitness.Budget :=
    { maxIntermediate := 100000, maxCertificate := 65536 }
  let .ok w := PolyDet.produce budget 4 (PolyDet.check 4) rows
    | throw (IO.userError "witness production failed")
  let a := rows.map (List.map PolyDet.toList)
  let w := w.map PolyDet.toList
  let products := PolyDet.Packed.products (PolyDet.ops 2) 4 a w
  let obligations := products.flatMap fun p =>
    (List.range p.width).map fun j =>
      (p.left, p.right.map (fun r => r.getD j []), p.result.getD j [])
  IO.println <| "FIXTURE " ++ (Lean.toJson obligations).compress

#eval exportFixture

end Determinant
