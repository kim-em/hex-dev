/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Hex.Conformance.Emit
import HexGroebner.Fixtures

/-! Deterministic matrix fixtures for independent row-space and provenance replay. -/

namespace Hex.Groebner.Emit
open Fixtures Hex.Conformance.Emit

private def array (items : Array String) : String :=
  "[" ++ String.intercalate "," items.toList ++ "]"

private def matrix (rows : Array (Array UInt64)) : String :=
  array (rows.map fun row => array (row.map (toString ·.toNat)))

private def dense (field : PrimeField) (columns : Nat) (row : SparseRow) : Array UInt64 :=
  (row.entries field).foldl (fun acc (i, c) => acc.set! i c) (Array.replicate columns 0)

private def op : RowOp → String
  | .input row => s!"[0,{row}]"
  | .addScaled left right c => s!"[1,{left},{right},{c.toNat}]"
  | .scale row c => s!"[2,{row},{c.toNat}]"

private def emitAll : IO Unit := do
  for field in fields do
    for c in cases field do
      let r ← match run field c with
        | .ok r => pure r
        | .error e => throw (IO.userError e)
      let e ← match r.result with
        | .ok e => pure e
        | .error err => throw (IO.userError (reprStr err))
      let reducers ← match sparse field c.columns c.reducers with
        | .ok r => pure r
        | .error e => throw (IO.userError e)
      let targets ← match sparse field c.columns c.targets with
        | .ok r => pure r
        | .error e => throw (IO.userError e)
      let remainders ← match (reduceRowsWith field {} c.columns reducers targets true).result with
        | .ok r => pure r
        | .error e => throw (IO.userError (reprStr e))
      let value := "{" ++
        s!"\"p\":{field.modulus.toNat},\"columns\":{c.columns}," ++
        "\"reducers\":" ++ matrix c.reducers ++ ",\"targets\":" ++ matrix c.targets ++
        ",\"rows\":" ++ matrix (e.rows.map fun p => dense field c.columns p.row) ++
        s!",\"reducerRank\":{e.reducerRank},\"fromTarget\":" ++
        array (e.rows.map fun p => if p.fromTarget then "true" else "false") ++
        ",\"trace\":" ++ array (e.trace.map op) ++
        ",\"refs\":" ++ array (e.rows.map fun p => p.derivation.elim "null" toString) ++
        ",\"remainders\":" ++ matrix (remainders.rows.map fun r => dense field c.columns r.row) ++
        ",\"remainderTrace\":" ++ array (remainders.trace.map op) ++
        ",\"remainderRefs\":" ++ array (remainders.rows.map fun r => r.derivation.elim "null" toString) ++ "}"
      emitResult "HexGroebner" s!"p{field.modulus.toNat}/{c.name}" "eliminate" value

end Hex.Groebner.Emit

def main : IO Unit := Hex.Groebner.Emit.emitAll
