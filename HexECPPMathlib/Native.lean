/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexECPPMathlib.Compact
import HexECPP.Search
import Lean.Meta.Tactic.TryThis

/-!
# Explicit native ECPP production

Native search takes only a subject, seed and finite allocation. Suggestions
and exports freeze replay inputs and an explicit terminal PrimeCert. Neither
CM search nor an external program runs while replaying frozen output.
-/

open Lean Elab Meta

namespace Hex.ECPP.Native

/-- Generate raw data and kernel-check the unconditional proof before any
suggestion or export. Proof elaboration remains in the optional bridge. -/
meta def generate (n : Nat) (seed : Nat := 0) (budget : SearchBudget := {}) :
    MetaM (String × Cert) := do
  if budget.maxBits > 256 then
    throwError "native ECPP: native production is admitted only through 256 bits"
  let c ← match (produce n seed budget).result with
    | .ok c => pure c
    | .error e => throwError "native ECPP: exhausted {repr e.resource}; unresolved subject {e.subject}; seed {seed}"
  let proof ← certProof c n (mkNatLit n)
  checkWithKernel proof
  let source := frozenRows c
  -- The public compact representation must itself fit its conversion budget.
  match convertText defaultImportBudget source (terminalCert c) with
  | .error e => throwError "native ECPP: frozen conversion failed at row {e.row}: {repr e.kind}"
  | .ok frozen =>
    unless checkAt n frozen do throwError "native ECPP: frozen certificate failed checkAt"
  return (source, c)

syntax (name := nativeSuggestTac) "primality?" " (" &"method" " := " &"ecpp" ")"
  (" (" &"seed" " := " num ")")? : tactic

set_option hygiene false in
@[tactic nativeSuggestTac] meta def suggest : Tactic.Tactic := fun stx => do
  let `(tactic| primality? (method := ecpp) $[(seed := $seed:num)]?) := stx
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
    let (source, cert) ← generate n seed
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

syntax (name := nativeExportCmd) "#ecpp_export" " (" &"method" " := " &"ecpp" ") "
  (" (" &"seed" " := " num ")")? ident ident " for " term : command

@[command_elab nativeExportCmd] meta def exportCert : Command.CommandElab := fun stx => do
  let `(command| #ecpp_export (method := ecpp) $[(seed := $seed:num)]? $mod:ident $decl:ident for $term:term) := stx
    | throwUnsupportedSyntax
  let seed := seed.map TSyntax.getNat |>.getD 0
  exportCertificate mod decl term (fun n => generate n seed)

end Hex.ECPP.Native
