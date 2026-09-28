/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.Compact
import Lean.Elab.Command
import Lean.Meta.Tactic.TryThis

/-!
# Explicit PARI certificate production

`primality? (method := pari)` calls `gp` on PATH and suggests a compact,
frozen certificate. `#ecpp_export Module.Name certName for n` writes a reusable
Lean module. Importing that module and replaying suggestions never calls PARI.
-/

open Lean Elab Meta

namespace Hex.ECPP.Pari

/-- Finite process limits; parser and proof limits apply independently. -/
structure ProcessBudget where
  timeoutMs : Nat := 30000
  maxOutputBytes : Nat := 16448
  maxErrorBytes : Nat := 4096
  stackBytes : Nat := 64000000
deriving Repr

private def readBounded (handle : IO.FS.Handle) (limit : Nat) : IO String := do
  let mut data := ByteArray.empty
  repeat
    let chunk ← handle.read 4096
    if chunk.isEmpty then
      let some text := String.fromUTF8? data
        | throw <| IO.userError "PARI output is not UTF-8"
      return text
    if data.size + chunk.size > limit then
      throw <| IO.userError s!"PARI output exceeds {limit} bytes"
    data := data ++ chunk

private def stop {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg) : IO Unit := do
  try child.kill catch _ => pure ()
  IO.sleep 100
  -- On POSIX, kill the entire session, including descendants holding pipes.
  if !System.Platform.isWindows then
    try
      discard <| IO.Process.output { cmd := "kill", args := #["-KILL", "--", s!"-{child.pid}"] }
    catch _ => pure ()
  try discard <| child.wait catch _ => pure ()

/-- Run only the evaluated natural numeral, without a shell or user startup file.
The injectable executable and budget are used by process conformance tests. -/
def run (n : Nat) (budget : ProcessBudget := {}) (executable : String := "gp")
    (cancel : Option IO.CancelToken := none) : IO String := do
  if HexArith.bitLength n > maxBits then
    throw <| IO.userError s!"PARI: subject exceeds the {maxBits}-bit replay limit"
  let child ← try
    IO.Process.spawn {
      cmd := executable
      args := #["-q", "-f", "-s", toString budget.stackBytes]
      stdin := .piped
      stdout := .piped
      stderr := .piped
      setsid := true }
  catch err =>
    throw <| IO.userError s!"PARI: cannot start `{executable}`; install PARI/GP and put `gp` on PATH ({err})"
  let (input, child) ← child.takeStdin
  let stdout ← IO.asTask (readBounded child.stdout budget.maxOutputBytes) .dedicated
  let stderr ← IO.asTask (readBounded child.stderr budget.maxErrorBytes) .dedicated
  let start ← IO.monoMsNow
  let completed ← IO.mkRef false
  try
    do
      let input := input
      input.putStr s!"print(\"HEX_ECPP_BEGIN\"); print(primecert({n})); print(\"HEX_ECPP_END\"); quit\n"
      input.flush
    repeat
      if let some cancel := cancel then
        if ← cancel.isSet then throw <| IO.userError "PARI: certificate generation cancelled"
      if (← IO.monoMsNow) - start ≥ budget.timeoutMs then
        throw <| IO.userError s!"PARI: certificate generation timed out after {budget.timeoutMs} ms"
      let outDone ← IO.hasFinished stdout
      let errDone ← IO.hasFinished stderr
      if outDone then
        if let .error err := stdout.get then throw err
      if errDone then
        if let .error err := stderr.get then throw err
      if let some status ← child.tryWait then
        if outDone && errDone then
          completed.set true
          let output ← IO.ofExcept stdout.get
          let errors ← IO.ofExcept stderr.get
          if status == 255 && (errors.splitOn "could not execute external process").length > 1 then
            throw <| IO.userError s!"PARI: cannot start `{executable}`; install PARI/GP and put `gp` on PATH"
          if status != 0 || !errors.trimAscii.toString.isEmpty then
            throw <| IO.userError s!"PARI: gp failed (exit {status}): {errors}"
          let lines := output.trimAscii.toString.splitOn "\n"
          unless lines.head? == some "HEX_ECPP_BEGIN" && lines.getLast? == some "HEX_ECPP_END" do
            throw <| IO.userError "PARI: malformed or incomplete output framing"
          let payload := String.intercalate "\n" (lines.drop 1 |>.dropLast)
          if payload.trimAscii.toString == "0" then
            throw <| IO.userError s!"PARI: {n} is not prime"
          return payload
      IO.sleep 25
  finally
    unless ← completed.get do stop child

private meta def subject (e : Expr) : MetaM Nat := do
  Hex.PrimalityTactic.checkClosed "PARI" e
  let some n ← getNatValue? (← whnf e)
    | throwError "PARI: expected a closed, transparent natural-number expression"
  unless ← isDefEq e (mkNatLit n) do
    throwError "PARI: subject must be definitionally transparent"
  if HexArith.bitLength n > maxBits then
    throwError "PARI: subject exceeds the {maxBits}-bit replay limit"
  return n

/-- Complete and kernel-check a PARI certificate before publishing any result. -/
meta def generate (n : Nat) : MetaM (String × Cert) := do
  let source ← run n (cancel := (← readThe Core.Context).cancelTk?)
  let cert ← match ← convertSupplied source with
    | .ok cert => pure cert
    | .error err => throwError "PARI conversion: row {err.row}: {repr err.kind}"
  let proof ← certProof cert n (mkNatLit n)
  checkWithKernel proof
  return (source, cert)

syntax (name := pariSuggestTac) "primality?" " (" &"method" " := " &"pari" ")" : tactic

set_option hygiene false in
@[tactic pariSuggestTac] meta def suggest : Tactic.Tactic := fun stx => do
  let goal ← Tactic.getMainGoal
  goal.withContext <| withOptions (maxRecDepth.set · 65536) do
    let target ← instantiateMVars (← goal.getType)
    let core := target.getAppFn.isConstOf ``Hex.Nat.Prime
    unless (target.getAppFn.isConstOf ``_root_.Nat.Prime || core) && target.getAppNumArgs == 1 do
      throwError "primality? (method := pari): expected a Nat.Prime or Hex.Nat.Prime goal"
    let nE := target.appArg!
    let n ← subject nE
    let (source, cert) ← generate n
    let compact ← compactSyntax source cert
    let replacement ← if core then
      `(tactic| exact Hex.Nat.prime_iff.mpr (by ecpp using ($compact)))
    else `(tactic| ecpp using ($compact))
    let proof ← certProof cert n nE
    let proof ← if core then
      mkAppM ``Iff.mpr #[mkApp (mkConst ``Hex.Nat.prime_iff) nE, proof]
    else pure proof
    goal.assign proof
    Tactic.replaceMainGoal []
    Meta.Tactic.TryThis.addSuggestion stx replacement

/-- Write one exposed certificate declaration in a user-selected module.
Creation is exclusive: existing files are never overwritten. -/
syntax (name := pariExportCmd) "#ecpp_export " ident ident " for " term : command

set_option hygiene false in
@[command_elab pariExportCmd] meta def exportCert : Command.CommandElab := fun stx => do
  let `(command| #ecpp_export $mod:ident $decl:ident for $term:term) := stx
    | throwUnsupportedSyntax
  let modName := mod.getId
  let declName := decl.getId
  let valid := fun (s : String) => s != "_" &&
    (s.toList.head?.any (fun c => c.isAlpha || c == '_')) &&
    s.toList.all (fun c => c.isAlphanum || c == '_')
  unless modName.toString.splitOn "." |>.all valid do
    throwError "#ecpp_export: module name must consist of ASCII identifier components"
  unless declName.isAtomic && valid declName.toString do
    throwError "#ecpp_export: declaration name must be an identifier without a namespace"
  let path := System.FilePath.mk ((modName.toString.replace "." "/") ++ ".lean")
  if ← path.pathExists then throwError "#ecpp_export: {path} already exists"
  let (source, cert) ← Command.liftTermElabM do
    let e ← Term.elabTermEnsuringType term (mkConst ``Nat)
    Term.synthesizeSyntheticMVarsNoPostponing
    let n ← subject (← instantiateMVars e)
    generate n
  let fullName := modName ++ declName
  let literal ← Command.liftTermElabM <| compactSyntax source cert
  let definition ← `(command| def $(mkIdent fullName):ident : Hex.ECPP.Cert := $literal)
  let rendered ← Command.liftTermElabM <| PrettyPrinter.ppCommand definition
  let body := s!"import HexECPPMathlib.Compact\n\n{rendered}\n"
  if let some parent := path.parent then IO.FS.createDirAll parent
  let handle ← IO.FS.Handle.mk path .writeNew
  handle.putStr body
  handle.flush
  logInfo m!"Wrote {path}. Add `import {modName}` at the top of your file, then use `ecpp using {fullName}`. Remove the export command after generation."

end Hex.ECPP.Pari
