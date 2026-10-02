/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSignDet.Codec.Value
import Lean.Data.Json

/-! Line-oriented conformance transport. Each request is a JSON array of byte
values. The standard Lean parser handles only that transport; the independent
oracle compares the new parser on the enclosed bytes. -/
namespace Hex.SignDet.JsonBytesDriver
open Lean

private def run (request : String) : Except String Json := do
  let values ← fromJson? (α := Array Nat) (← Json.parse request)
  if !values.all (· < 256) then throw "transport byte out of range"
  let bytes := ByteArray.mk (values.map UInt8.ofNat)
  match Codec.Json.readBytes bytes with
  | none => return toJson #[toJson "error"]
  | some value =>
    if Codec.Json.readBytes value.writeBytes != some value then
      throw "literal roundtrip failed"
    let some text := String.fromUTF8? value.writeBytes | throw "printer emitted invalid UTF-8"
    return toJson #[toJson "ok", toJson text]

end Hex.SignDet.JsonBytesDriver

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    match Hex.SignDet.JsonBytesDriver.run line with
    | .ok result => output.putStrLn result.compress
    | .error message => throw (IO.userError message)
