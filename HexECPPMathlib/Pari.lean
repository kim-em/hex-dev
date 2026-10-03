/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPPMathlib.Compact
public import HexECPPMathlib.Pari.Process
public meta import HexECPPMathlib.Pari.Process
public import Lean.Elab.Command
public import Lean.Meta.Tactic.TryThis

/-!
# Explicit PARI certificate production

`primality? (method := pari)` calls `gp` on PATH and suggests a compact,
frozen certificate. In a batch build, `#ecpp_export Module.Name certName for n`
writes a reusable Lean module. The language server displays build instructions.
Importing that module and replaying suggestions never calls PARI.
-/

@[expose] public section

open Lean Elab Meta

namespace Hex.ECPP.Pari

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
  validateCert cert
  let frozen ← match convertText defaultImportBudget source (terminalCert cert) with
    | .ok frozen => pure frozen
    | .error err => throwError "PARI frozen conversion: row {err.row}: {repr err.kind}"
  let proof ← certProof frozen n (mkNatLit n)
  checkWithKernel proof
  return (source, frozen)

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
  exportCertificate mod decl term generate

end Hex.ECPP.Pari
