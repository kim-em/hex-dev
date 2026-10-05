/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexPermGroup
public meta import Lean
public section

open Lean Elab Command

/-- Elaborate the command's printed source, so its certificate proofs and final
statement are checked exactly as they would be in a downstream file. -/
syntax "#replay_perm_group_certificate " ident " for " term : command

elab_rules : command
  | `(#replay_perm_group_certificate $name:ident for $s:term) => do
    let messages := (← get).messages
    modify fun state => { state with messages := {} }
    elabCommand (← `(#perm_group_certificate $name for $s))
    let output := (← get).messages
    modify fun state => { state with messages }
    if output.hasErrors then
      modify fun state => { state with messages := messages ++ output }
      return
    let [message] := output.toList
      | throwError "expected exactly one certificate source message"
    let source ← message.data.toString
    let input := Parser.mkInputContext source "<perm_group_certificate>"
    let mut parserState : Parser.ModuleParserState := {}
    repeat
      let (stx, next, errors) := Parser.parseCommand input
        { env := ← getEnv, options := ← getOptions } parserState {}
      if errors.hasErrors then throwError "certificate output does not parse"
      if Parser.isTerminalCommand stx then break
      withReader (fun ctx => { ctx with fileName := input.fileName, fileMap := input.fileMap }) do
        elabCommand stx
      if (← get).messages.hasErrors then
        throwError "certificate output does not elaborate"
      parserState := next

namespace Hex.PermGroup.CertificateTests

def gens : Array (Perm 3) :=
  #[Perm.ofImages 3 [1, 2, 0], Perm.ofImages 3 [1, 0, 2]]

#replay_perm_group_certificate literal for
  #[Perm.ofImages 3 [1, 2, 0], Perm.ofImages 3 [1, 0, 2]]
#replay_perm_group_certificate definition for gens
#replay_perm_group_certificate fallback for #[Perm.ofImages 3 [0, 0, 1]]
example : HasOrder gens 6 := definition_hasOrder
example : HasOrder #[Perm.ofImages 3 [0, 0, 1]] 1 := fallback_hasOrder

end Hex.PermGroup.CertificateTests
