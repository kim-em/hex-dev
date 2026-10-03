/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexECPPMathlib.Compact
public import HexECPP.Search
public meta import HexECPP.Search
public import Lean.Meta.Tactic.TryThis
public import Mathlib.Tactic.Linter.TacticDocumentation

/-!
# Explicit native ECPP production

Native search takes only a subject, seed and finite allocation. Suggestions
and exports freeze replay inputs and an explicit terminal PrimeCert. Neither
CM search nor an external program runs while replaying frozen output.
-/

@[expose] public section

open Lean Elab Meta

namespace Hex.ECPP.Native

/-- Generate raw data and kernel-check the unconditional proof before any
suggestion or export. Proof elaboration remains in the optional bridge. -/
meta def generate (n : Nat) (seed : Nat := 0) (budget : SearchBudget := {}) :
    MetaM (String × Cert) := do
  if budget.maxBits > 512 then
    throwError "native ECPP: native production is admitted only through 512 bits"
  let budget := if budget.maxBits > 256 then
    { budget with
      maxDepth := min budget.maxDepth (defaultImportBudget.maxRows + 1)
      maxRows := some (min (budget.maxRows.getD defaultImportBudget.maxRows) defaultImportBudget.maxRows)
      maxNodes := some (min (budget.maxNodes.getD 32) 32)
      backtrackOutput := true }
    else { budget with maxDepth := min budget.maxDepth defaultImportBudget.maxRows }
  let c ← match (produce n seed budget).result with
    | .ok c => pure c
    | .error e => throwError "native ECPP: no certificate; stopped at {repr e.resource}; unresolved subject {e.subject}; seed {seed}"
  validateCert c
  let source := frozenRows c
  -- The public compact representation must itself fit its conversion budget.
  let frozen ← match convertText defaultImportBudget source (terminalCert c) with
  | .error e => throwError "native ECPP: frozen conversion failed at row {e.row}: {repr e.kind}"
  | .ok frozen => pure frozen
  let proof ← certProof frozen n (mkNatLit n)
  checkWithKernel proof
  return (source, frozen)

/-- Select an explicit policy without changing ordinary primality dispatch. -/
meta def selectBudget (bits : Nat) : MetaM SearchBudget :=
  if bits == 256 then pure {} else if bits == 512 then pure public512Budget
  else throwError "native ECPP: bits must be 256 or 512"

/-- Explicit bounded native ECPP production with a kernel-checked frozen suggestion.
The optional seed controls untrusted proposal search, not proof acceptance. -/
tactic_extension Hex.PrimalityTactic.primalitySuggestTac

@[inherit_doc Hex.PrimalityTactic.primalitySuggestTac,
  tactic_alt Hex.PrimalityTactic.primalitySuggestTac]
syntax (name := nativeSuggestTac) "primality?" " (" &"method" " := " &"ecpp" ")"
  (atomic(" (" &"bits" " := ") num ")")?
  (" (" &"seed" " := " num ")")? : tactic

set_option hygiene false in
/-- Solve the closed subject and suggest its exact compact replay term. -/
@[tactic nativeSuggestTac] meta def suggest : Tactic.Tactic := fun stx => do
  let `(tactic| primality? (method := ecpp) $[(bits := $bits:num)]? $[(seed := $seed:num)]?) := stx
    | throwUnsupportedSyntax
  let seed := seed.map TSyntax.getNat |>.getD 0
  let goal ← Tactic.getMainGoal
  goal.withContext <| withOptions (maxRecDepth.set · 65536) do
    let target ← instantiateMVars (← goal.getType)
    let core := target.getAppFn.isConstOf ``Hex.Nat.Prime
    unless (target.getAppFn.isConstOf ``_root_.Nat.Prime || core) && target.getAppNumArgs == 1 do
      throwError "primality? (method := ecpp): expected a Nat.Prime or Hex.Nat.Prime goal"
    let nE := target.appArg!
    Hex.PrimalityTactic.checkClosed "native ECPP" nE
    let some n ← getNatValue? (← whnf nE)
      | throwError "native ECPP: expected a closed natural-number numeral"
    unless ← isDefEq nE (mkNatLit n) do
      throwError "native ECPP: subject must be definitionally transparent"
    let budget ← selectBudget (bits.map TSyntax.getNat |>.getD 256)
    let (source, cert) ← generate n seed budget
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

/-- Export a new module containing a kernel-checked native ECPP certificate. -/
syntax (name := nativeExportCmd) "#ecpp_export" " (" &"method" " := " &"ecpp" ") "
  (atomic(" (" &"bits" " := ") num ")")?
  (" (" &"seed" " := " num ")")? ident ident " for " term : command

/-- Run native generation for the explicit batch-only exclusive export command. -/
@[command_elab nativeExportCmd] meta def exportCert : Command.CommandElab := fun stx => do
  let `(command| #ecpp_export (method := ecpp) $[(bits := $bits:num)]? $[(seed := $seed:num)]? $mod:ident $decl:ident for $term:term) := stx
    | throwUnsupportedSyntax
  let seed := seed.map TSyntax.getNat |>.getD 0
  Command.liftTermElabM do
    let _ ← selectBudget (bits.map TSyntax.getNat |>.getD 256)
    pure ()
  exportCertificate mod decl term (fun n => do
    let budget ← selectBudget (bits.map TSyntax.getNat |>.getD 256)
    generate n seed budget)

end Hex.ECPP.Native
