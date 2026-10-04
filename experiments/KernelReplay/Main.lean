/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Lean
public meta import KernelReplay.ProofProbe

public meta section

open Lean Elab
open Hex.SignDet

mutual
private def jsonTerm : Codec.Json → String
  | .null => "Hex.SignDet.Codec.Json.Value.null"
  | .bool b => "(Hex.SignDet.Codec.Json.Value.bool " ++ toString b ++ ")"
  | .number n => "(Hex.SignDet.Codec.Json.Value.number (" ++ toString n ++ "))"
  | .string value => "(Hex.SignDet.Codec.Json.Value.string " ++ reprStr value ++ ")"
  | .array values => "(Hex.SignDet.Codec.Json.Value.array " ++ valuesTerm values ++ ")"
  | .object fields => "(Hex.SignDet.Codec.Json.Value.object " ++ fieldsTerm fields ++ ")"
private def valuesTerm : Codec.Json.Values → String
  | .nil => "Hex.SignDet.Codec.Json.Values.nil"
  | .cons value rest => "(Hex.SignDet.Codec.Json.Values.cons " ++ jsonTerm value ++
      " " ++ valuesTerm rest ++ ")"
private def fieldsTerm : Codec.Json.Fields → String
  | .nil => "Hex.SignDet.Codec.Json.Fields.nil"
  | .cons key value rest => "(Hex.SignDet.Codec.Json.Fields.cons " ++ reprStr key ++
      " " ++ jsonTerm value ++ " " ++ fieldsTerm rest ++ ")"
end

/-- Run the proof assembler on fixed controls or a quoted JSON record. This
experiment is not a public certificate byte reader. -/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules (loadExts := true) #[{ module := `KernelReplay.ProofProbe }] {}
  if let ["emit", path] := args then
    IO.FS.writeBinFile path Hex.RealClosure.Algebraic.KernelReplayProofProbe.graphJson.writeBytes
    return 0
  let controls : List (String × String × String × Option String) := [
    ("complete", "completeGraph", "true", none),
    ("missing", "missingGraph", "unproved", none),
    ("false", "falseGraph", "false", none),
    ("memo", "completeMemo", "true", none)]
  let byteControl ← match args with
    | ["bytes-equal", path] => do
      let json ← match Codec.parse {} (← IO.FS.readBinFile path) with
        | .ok value => pure value
        | .error message => throw (IO.userError message)
      pure (some ("bytes-equal", "byteEqual " ++ jsonTerm json, "true", none))
    | [command, path, mode, expected] => do
      unless ["bytes", "bytes-bound", "bytes-read"].contains command do
        throw (IO.userError "expected bytes, bytes-bound, or bytes-read")
      let json ← match Codec.parse {} (← IO.FS.readBinFile path) with
        | .ok value => pure value
        | .error message => throw (IO.userError message)
      let facts ← match mode with
        | "full" => pure "fullJsonFacts"
        | "missing" => pure "missingJsonFacts"
        | _ => throw (IO.userError "expected full or missing coefficient facts")
      unless ["true", "false", "unproved"].contains expected do
        throw (IO.userError "expected true, false, or unproved outcome")
      let literal := if command == "bytes-bound" then some (jsonTerm json) else none
      let reader := if command == "bytes-read" then "readJson" else "checkJson"
      pure (some (command, reader ++ " Hex.RealClosure.Algebraic.KernelReplayProofProbe." ++
        facts ++ " " ++ jsonTerm json, expected, literal))
    | _ => pure none
  if byteControl.isNone && args.any (fun arg => !controls.any (fun control => control.1 == arg)) then
    throw (IO.userError "unknown control name")
  let selected := match byteControl with
    | some control => [control]
    | none => controls.filter fun control => args.isEmpty || args.contains control.1
  if selected.isEmpty then
    (← IO.getStderr).putStrLn "expected complete, missing, false, or memo"
    return 2
  for (label, term, outcome, literal) in selected do
    IO.println s!"control={label}"
    let input := "#proof_probe Hex.RealClosure.Algebraic.KernelReplayProofProbe." ++
      term ++ " expecting \"" ++ outcome ++ "\"" ++
        (literal.map (" binding " ++ ·)).getD ""
    let parsedCommand ← match Parser.runParserCategory env `command input with
      | .ok parsedCommand => pure parsedCommand
      | .error message => throw (IO.userError message)
    let options := maxHeartbeats.set (maxRecDepth.set {} 32768) 1000000
    let state := Command.mkState env {} options
    let context : Command.Context := {
      fileName := label
      fileMap := FileMap.ofString input
      snap? := none
      cancelTk? := none }
    let result ← EIO.toIO' ((Command.elabCommand parsedCommand context).run state)
    match result with
    | .error error => throw (IO.userError (← error.toMessageData.toString))
    | .ok (_, state) =>
      for message in state.messages.toList do
        IO.println (← message.toString)
      if state.messages.hasErrors then return 1
  return 0
