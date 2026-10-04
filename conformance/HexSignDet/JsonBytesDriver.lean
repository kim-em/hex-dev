/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module
public import HexSignDet.Codec.Value
public import HexSignDet.JsonBytes
public import HexSignDet.Codec.Bytes
public import Lean.Data.Json

public section

/-! Line-oriented conformance transport. Each request is a JSON array of byte
values. The standard Lean parser handles only that transport; the independent
oracle compares the new parser on the enclosed bytes. -/
namespace Hex.SignDet.JsonBytesDriver
open Lean

mutual
/-- Inspect the parsed constructors directly, independently of the byte printer. -/
private def inspect : Codec.Json.Value → Json
  | .null => .arr #[toJson "null"]
  | .bool b => .arr #[toJson "bool", toJson b]
  | .number n => .arr #[toJson "int", toJson n]
  | .string s => .arr #[toJson "string", toJson s]
  | .array vs => .arr #[toJson "array", .arr (inspectValues vs).toArray]
  | .object fs => .arr #[toJson "object", .arr (inspectFields fs).toArray]
private def inspectValues : Codec.Json.Values → List Json
  | .nil => []
  | .cons v vs => inspect v :: inspectValues vs
private def inspectFields : Codec.Json.Fields → List Json
  | .nil => []
  | .cons key v fs => .arr #[.arr #[toJson "string", toJson key], inspect v] :: inspectFields fs
end

private def run (request : String) : Except String Json := do
  let values ← fromJson? (α := Array Nat) (← Json.parse request)
  if !values.all (· < 256) then throw "transport byte out of range"
  let bytes := ByteArray.mk (values.map UInt8.ofNat)
  match Codec.Json.readBytes bytes with
  | none => return toJson #[toJson "error"]
  | some value =>
    let printed := value.writeBytes
    if Codec.Json.readBytes printed != some value then
      throw "literal roundtrip failed"
    let some text := String.fromUTF8? printed | throw "printer emitted invalid UTF-8"
    return toJson #[toJson "ok", toJson text, inspect value]

end Hex.SignDet.JsonBytesDriver

private def runLines : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    match Hex.SignDet.JsonBytesDriver.run line with
    | .ok result => output.putStrLn result.compress
    | .error message => throw (IO.userError message)

/-- File mode avoids an unrelated JSON transport when checking large native inputs. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["--stack-canary"] => IO.println (← Hex.SignDet.JsonBytes.stackCanary 1000000)
  | [] => runLines
  | ["--check-file", source] =>
    let bytes ← IO.FS.readBinFile source
    match Hex.SignDet.Codec.checkBytes {} bytes with
    | .error message => throw (IO.userError message)
    | .ok () => pure ()
  | ["--file", source, target] =>
    let bytes ← IO.FS.readBinFile source
    match Hex.SignDet.Codec.checkBytes {} bytes with
    | .error message => throw (IO.userError message)
    | .ok () => pure ()
    let some value := Hex.SignDet.Codec.Json.readBytes bytes
      | throw (IO.userError "JSON input rejected")
    IO.FS.writeBinFile target value.writeBytes
  | _ => throw (IO.userError "expected no arguments, --stack-canary, --check-file SOURCE, or --file SOURCE TARGET")
